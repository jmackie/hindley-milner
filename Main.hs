{-# LANGUAGE DefaultSignatures          #-}
{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE OverloadedLists            #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE ScopedTypeVariables        #-}

{-# OPTIONS -Wall #-}

module Main where

import Prelude

import Control.Applicative (liftA2)
import Control.Arrow ((>>>))
import Control.Comonad (extract)
import Control.Comonad.Cofree (Cofree((:<)))
import qualified Control.Comonad.Trans.Cofree as Trans.Cofree
import Control.Monad.Except (MonadError, throwError)
import Data.Functor.Foldable (Fix(Fix), cata, unfix)
import Data.List.NonEmpty (NonEmpty((:|)))
import qualified Data.List.NonEmpty as NonEmpty
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as Text.IO
import Lens.Family (ASetter, over, views)

import Control.Monad.RWS.Strict
    ( MonadReader
    , MonadState
    , MonadWriter
    , RWST
    , ask
    , get
    , listen
    , local
    , put
    , runRWST
    , tell
    )


type Ident 
    = Text


-- | Base expression functor.
data Expr r
    = App r r
    | Abs Ident r
    | Var Ident
    | Lit (Literal r)
    deriving (Functor)


data Literal a
    = IntLiteral Integer
    | FloatLiteral Double
    | StringLiteral Text
    | BoolLiteral Bool
    | ArrayLiteral [a]
    deriving (Functor)


-- | Polytype.
data Scheme 
    = Forall (Set TVar) Type
    deriving (Show)


-- | Monotype.
data Type 
    = FunctionType Type Type
    | VarType TVar
    | PrimType (Prim Type)
    deriving (Show, Eq)


data Prim ty
    = IntType
    | FloatType
    | StringType
    | BoolType
    | ArrayType ty
    deriving (Show, Eq, Functor)


-- | Traversal over the immediate sub-types of a 'Type'.
subTypes :: Applicative f => (Type -> f Type) -> Type -> f Type
subTypes f = \case
    FunctionType x y -> FunctionType <$> f x <*> f y
    VarType tv -> pure (VarType tv)
    PrimType (ArrayType vt) -> PrimType . ArrayType <$> f vt
    PrimType prim -> pure (PrimType prim)


newtype TVar = TV { unTVar :: Integer }
    deriving stock (Show)
    deriving newtype (Eq, Ord, Enum)


-- | Constraints need to be solved.
data Constraint 
    = EqConstraint Type Type


pattern (:~) :: Type -> Type -> Constraint
pattern (:~) a b = EqConstraint a b
{-# COMPLETE (:~) #-} 


-- | All the types that we know about at any given time.
type Env = Map Ident Scheme 


-- | A type substitution. 
--
-- Applying this means "substitute all occurences of the type variable (key) 
-- with the corresponding type".
--
-- Inference generates constraints, constraints are solved/unified to a 
-- substitution.
type Subst = Map TVar Type


class Monad m => MonadSupply m where
    fresh :: m Integer
    peek  :: m Integer

    default fresh :: MonadState Integer m => m Integer
    fresh = do
        i <- get
        put (i + 1)
        pure i

    default peek :: MonadState Integer m => m Integer
    peek = get


-- | spit out a fresh type variable.
freshType :: MonadSupply m => m Type
freshType = VarType . TV <$> fresh


newtype Infer a = Infer (RWST Env [Constraint] Integer (Either InferError) a)
    deriving anyclass ( MonadSupply )
    deriving newtype  ( Functor, Applicative, Monad     
                      , MonadState Integer               -- hella deriving
                      , MonadReader Env
                      , MonadWriter [Constraint]
                      , MonadError InferError
                      )


runInfer :: Infer a -> Env -> Either InferError a
runInfer (Infer m) env = do 
    (a, _, _) <- runRWST m env 0 
    pure a


-- | Things that can go wrong while inferring.
data InferError
    = UnificationError Type Type
    | UnknownVariable Ident Env
    | InfiniteType TVar Type 
    | DodgyArray [Type]
    deriving (Show)


-- | Add type annotations to an expression tree.
annotate :: Fix Expr -> Infer (Cofree Expr Type)
annotate x' = do 
    (x, cs) <- listen (annotate' x')
    s <- solve cs
    pure (substitute s <$> x)


-- | Pepper the expression tree with mostly useless type variables, but collect
-- constraints so that we can substitute those variables.
annotate' :: Fix Expr -> Infer (Cofree Expr Type)
annotate' = unfix >>> \case
    Var ident -> do
        t <- lookupEnv ident
        pure (t :< Var ident)

    App f' x' -> do
        f <- annotate f'
        x <- annotate x'
        tv <- freshType
        tell [extract f :~ FunctionType (extract x) tv]
        pure (tv :< App f x)

    Abs ident x' -> do
        tv <- freshType
        x <- local (Map.insert ident (Forall [] tv)) (annotate x')
        pure (FunctionType tv (extract x) :< Abs ident x)

    Lit lit -> 
        case lit of
            IntLiteral integer -> 
                pure (PrimType IntType :< Lit (IntLiteral integer))

            FloatLiteral double -> 
                pure (PrimType FloatType :< Lit (FloatLiteral double))

            StringLiteral text -> 
                pure (PrimType StringType :< Lit (StringLiteral text))

            BoolLiteral bool -> 
                pure (PrimType BoolType :< Lit (BoolLiteral bool))

            ArrayLiteral [] -> do
                tv <- freshType 
                pure (PrimType (ArrayType tv) :< Lit (ArrayLiteral []))

            ArrayLiteral (v' : vs') -> do
                vs <- liftA2 (:|) (annotate v') (traverse annotate vs')
                case NonEmpty.nub (extract <$> vs) of
                    t :| [] ->
                        pure (PrimType (ArrayType t) :< Lit (ArrayLiteral []))

                    t :| ts ->
                        throwError (DodgyArray (t : ts))
        
  where
    lookupEnv :: Ident -> Infer Type
    lookupEnv ident = do
        env <- ask
        case Map.lookup ident env of
            Nothing -> throwError (UnknownVariable ident env)
            Just sc -> instantiate sc


-- | Attempt to resolve a bunch of type constraints to a subsitution.
solve :: forall m. MonadError InferError m => [Constraint] -> m Subst
solve = go mempty where
    go :: Subst -> [Constraint] -> m Subst
    go s [] = pure s
    go s1 (c : rest) = do
        s2 <- unify c
        go (s2 `Map.union` s1) (substitute s2 <$> rest)
        --          ^^^^^ NOTE: left-biased


-- | Unification attempts to generate the most general type substitution 
-- that arises from a constraint.
--
-- For example, try following through the case of @unify (a :~ Int)@. The most 
-- general type that satisfies both is @Int@, so we need a substitution that will 
-- convert all occurrences of @a@ to @Int@.
unify :: MonadError InferError m => Constraint -> m Subst
unify (t1 :~ t2) = case (t1, t2) of
    (VarType tv, t) -> bind tv t
    (t, VarType tv) -> bind tv t

    (FunctionType l r, FunctionType l' r') -> do
        s1 <- unify (l :~ l')
        s2 <- unify (substitute s1 r :~ substitute s1 r')
        pure (s2 `Map.union` s1)

    (PrimType a, PrimType b) | a == b -> return mempty

    (a, b) -> throwError (UnificationError a b)


bind :: MonadError InferError m => TVar -> Type -> m Subst
bind tv t 
    | t == VarType tv = return mempty                  -- no op: bound to self
    | tv `occursIn` t = throwError (InfiniteType tv t) -- occurs check
    | otherwise       = pure (Map.singleton tv t)      -- ok, substitution


-- | Occurs check.
occursIn :: FreeTVars a => TVar -> a -> Bool
occursIn tv a = tv `Set.member` ftv a


-- | Bind all quantified variables to 'fresh' type variables
instantiate :: MonadSupply m => Scheme -> m Type 
instantiate (Forall as t) = do
    s <- sequenceA $ Map.fromSet (const freshType) as -- freshies
    pure (substitute s t)


-- | Something is 'Substitutable' if we can apply a 'Subst'itution to it. 
class Substitutable a where
    -- a.k.a 'apply'
    substitute :: Subst -> a -> a


instance Substitutable Constraint where
    substitute s (x `EqConstraint` y) = 
        substitute s x `EqConstraint` substitute s y


instance Substitutable Type where
    substitute s t@(VarType tv) = Map.findWithDefault t tv s
    substitute s t = flip (rewriteOf subTypes) t $ \case
        VarType tv -> Map.lookup tv s
        _ -> Nothing


-- | This basically exists for overloading.
class FreeTVars a where
    ftv :: a -> Set TVar


instance FreeTVars Type where
    ftv (VarType tv) = [tv]
    ftv t = flip (views subTypes) t $ \case
        VarType tv -> [tv]
        _ -> mempty
        

-- <3
-- https://github.com/dhall-lang/dhall-haskell/pull/817


rewriteOf :: ASetter a b a b -> (b -> Maybe a) -> a -> b
rewriteOf l f = go where go = transformOf l (\x -> maybe x go (f x))


transformOf :: ASetter a b a b -> (b -> b) -> a -> b
transformOf l f = go where go = f . over l go


-- DEMO/TESTING


main :: IO ()
main = do
  either undefined Text.IO.putStrLn (prettyExpr <$> runInfer (annotate example1) mempty)
  either undefined Text.IO.putStrLn (prettyExpr <$> runInfer (annotate example2) mempty)

  where 

    -- EXAMPLES
    
    example1 :: Fix Expr
    example1 = 
        Fix (Abs "a" (Fix (Var "a")))

    example2 :: Fix Expr
    example2 = 
        Fix (App example1 (Fix (Lit (IntLiteral 42))))

    -- PRETTY PRINTING

    prettyExpr :: Cofree Expr Type -> Text
    prettyExpr = cata $ \case
        _ Trans.Cofree.:< Var ident -> 
            ident

        _ Trans.Cofree.:< App f x -> 
            f <> " " <> x

        FunctionType t _ Trans.Cofree.:< Abs arg x -> 
            "(\\(" <> arg <> " : " <> prettyType t <> ") -> " <> x <> ")"

        _ Trans.Cofree.:< Lit lit ->
            case lit of
                IntLiteral integer  -> Text.pack (show integer)
                FloatLiteral double -> Text.pack (show double)
                StringLiteral text  -> text
                BoolLiteral bool    -> if bool then "true" else "false"
                ArrayLiteral vs     -> "[" <> Text.intercalate ", " vs <> "]" 

        _ -> undefined

    prettyType :: Type -> Text
    prettyType = \case
        FunctionType x y -> 
            prettyType x <> " -> " <> prettyType y

        VarType _ -> 
            "*"

        PrimType prim -> 
            prettyPrim prettyType prim

    prettyPrim :: (a -> Text) -> Prim a -> Text
    prettyPrim pa = \case
        IntType -> "Int"
        FloatType -> "Float"
        StringType -> "String"
        BoolType -> "Bool"
        ArrayType a -> "Array " <> pa a

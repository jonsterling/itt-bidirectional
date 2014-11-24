{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UnicodeSyntax #-}

module TT.Judgement.Class where

import Control.Applicative
import Control.Monad.Error.Class
import Control.Monad.Trace.Class
import Data.Monoid
import Prelude.Unicode
import Unbound.LocallyNameless

import TT.Tm

-- | A judgement is given by its syntax @j@ and its synthesis @s@. An
-- "analytic" judgement produces trivial synthesis '()'.
class Judgement j s | j → s where
  judge
    ∷ MonadJudge m
    ⇒ j
    → m s

type MonadJudge m
  = ( MonadTrace TraceTag m
    , MonadError Refutation m
    , Applicative m
    , Alternative m
    , Monad m
    , Fresh m
    )

data TraceTag where
  Wellformedness ∷ TraceTag
  Assertion ∷ (Show j, Judgement j o) ⇒  j → TraceTag

data Refutation
  = NotImplemented
  | NotEqual Tm Tm
  | NoSuchVariable (Name Tm)
  | ExpectedPiType
  | ExpectedSumType
  | ExpectedIdentityType
  | ExpectedType
  | ExpectedUniverse
  | CompoundRefutation [Refutation]
  | InvalidUniverse
  | UniverseCycle
  deriving Show

instance Monoid Refutation where
  mempty = CompoundRefutation []
  mappend (CompoundRefutation rs) (CompoundRefutation rs') =
    CompoundRefutation $ mappend rs rs'
  mappend (CompoundRefutation rs) r =
    CompoundRefutation $ rs ++ [r]
  mappend r (CompoundRefutation rs) =
    CompoundRefutation $ r:rs
  mappend r r' =
    CompoundRefutation [r,r']

instance Show TraceTag where
  show (Assertion j) = "[" ++ show j ++ "]"
  show Wellformedness = "[wf]"

trace
  ∷ ( MonadTrace TraceTag m
    , Judgement j o
    , Show j
    )
  ⇒ j
  → m α
  → m α
trace = traceScope ∘ Assertion

wf
  ∷ MonadTrace TraceTag m
  ⇒ m α
  → m α
wf = traceScope Wellformedness

(<?>)
  ∷ MonadError e m
  ⇒ Maybe α
  → e
  → m α
Nothing <?> e = throwError e
Just a <?> _ = return a
infixl 8 <?>


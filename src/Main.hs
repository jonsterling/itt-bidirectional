{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE ViewPatterns #-}

-- A small bidirectional type checker for intensional intuitionistic type
-- theory, structured around judgements as an organizing principle. The
-- checking judgement ("M checks at type T") is analytic, and the inferring
-- judgement is synthetic ("M has a type").
--
-- It is written using Weirich's Unbound, mainly because it was easy enough to
-- use and fighting Bound to work with contexts was not something I wanted to
-- spend time on.
--
-- This has very good error-reporting: that is, all whenever we attempt to
-- verify a judgement, we leave a breadcrumb behind such that if we refute the
-- judgement, we know exactly where that occured.

module Main where

import Control.Applicative
import Control.Monad.Error.Class
import Control.Monad.Trace.Class
import Control.Monad.Trace.ErrorTrace
import Control.Monad.Trans
import Control.Monad.Trans.Trace
import Prelude.Unicode

import Unbound.LocallyNameless hiding (Equal, Refl, to)

import TT.Tm
import TT.Tele
import TT.Judgement.Class
import TT.Judgement.Hypothetical
import TT.Judgement.Bidirectional

newtype Judge α
  = Judge
  { _judge ∷ TraceT TraceTag Refutation FreshM α
  } deriving (Monad, Functor, Alternative, Applicative, MonadTrace TraceTag, MonadError Refutation)

instance Fresh Judge where
  fresh = Judge ∘ lift ∘ fresh

runJudge
  ∷ Judge α
  → Either (ErrorTrace TraceTag Refutation) α
runJudge = runFreshM ∘ runTraceT ∘ _judge

testFailure ∷ Judge ()
testFailure = judge $ Empty ⊢ Refl Ax :⇐ Id (Plus Unit Unit) (Ax,Ax)

testFailure2 ∷ Judge ()
testFailure2 = judge $ Empty ⊢ Inl Ax :⇐ Plus Unit Ax

test ∷ Judge ()
test = do
  let tm = Lam $ bind (string2Name "α") $
             Lam $ bind (string2Name "x") $
               Inl (V $ string2Name "x")
  let ty = Pi (Univ 0) $ bind (string2Name "α") $
             Pi (V $ string2Name "α") $ bind (string2Name "x") $
               Plus (V $ string2Name "α") Unit
  judge $ Empty ⊢ tm :⇐ ty

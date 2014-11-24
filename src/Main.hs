{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
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
import Control.Lens hiding (Contains)
import Control.Monad
import Control.Monad.Error.Class
import Control.Monad.Trace.Class
import Control.Monad.Trans.Maybe
import Data.Monoid
import Prelude.Unicode

import Unbound.LocallyNameless hiding (Equal, to)

data Tm
  = V (Name Tm)
  | App Tm Tm
  | Ann Tm Tm
  | Void
  | Unit
  | Ax
  | Univ Int
  | Plus Tm Tm
  | Pi Tm (Bind (Name Tm) Tm)
  | Lam (Bind (Name Tm) Tm)
  | Inl Tm
  | Inr Tm
  | Decide (Bind (Name Tm) Tm) Tm (Bind (Name Tm) Tm) (Bind (Name Tm) Tm)
  deriving Show

makePrisms ''Tm

data Hyp
  = Hyp (Name Tm) (Embed Tm)

instance Show Hyp where
  showsPrec i (Hyp x (Embed α)) =
    showParen (i > 10) $
      shows x ∘ (" : " ++) ∘ shows α

data Tele
  = Empty
  | Cons (Rebind Hyp Tele)

makePrisms ''Tele

pattern γ :> h ← Cons (unrebind → (h, γ))
pattern x :∈ α = Hyp x (Embed α)

instance Show Tele where
  showsPrec _ Empty = ("·" ++)
  showsPrec i (γ :> h) =
    showParen (i > 10) $
      shows γ ∘ (", " ++) ∘ shows h
  showsPrec _ _ = error "This is total"

(>:) ∷ Tele → Hyp → Tele
γ >: h = Cons $ rebind h γ

data Hypothetical j where
  Hypothetical
    ∷ Alpha j
    ⇒ Rebind j Tele
    → Hypothetical j

infixl 8 :⊢
pattern γ :⊢ j ← Hypothetical (unrebind → (j, γ))

data TraceTag where
  Wellformedness ∷ TraceTag
  Assertion ∷ (Show j, Judgement j o) ⇒  j → TraceTag

data Refutation
  = NotImplemented
  | NotEqual Tm Tm
  | NoSuchVariable (Name Tm)
  | ExpectedPiType
  | ExpectedSumType
  | CompoundRefutation [Refutation]
  | InvalidUniverse
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

type MonadJudge m
  = ( MonadTrace TraceTag m
    , MonadError Refutation m
    , Applicative m
    , Alternative m
    , Monad m
    , Fresh m
    )

-- | A judgement is given by its syntax @j@ and its synthesis @s@. An
-- "analytic" judgement produces trivial synthesis '()'.
class Judgement j s | j → s where
  judge
    ∷ MonadJudge m
    ⇒ j
    → m s

data Chk
  = Chk Tm Tm
data Inf
  = Inf Tm
  deriving Show
data Equal
  = Equal Tm (Tm, Tm)
data EqualTypes
  = EqualTypes Tm Tm
data Contains
  = Contains Tele (Name Tm)
data IsType
  = IsType Tm

infixl 9 :⇐
pattern m :⇐ α = Chk m α

infixl 9 :∋
pattern γ :∋ x = Contains γ x

instance Show Chk where
  showsPrec i (Chk m α) =
    showParen (i > 10) $
      shows m ∘ (" ⇐ " ++) ∘ shows α

instance Show Equal where
  showsPrec i (Equal α (m,n)) =
    showParen (i > 10) $
      shows m ∘ (" = " ++) ∘ shows n ∘ (" : " ++) ∘ shows α

instance Show EqualTypes where
  showsPrec i (EqualTypes α β) =
    showParen (i > 10) $
      shows α ∘ (" = " ++) ∘ shows β ∘ (" type" ++)

instance Show Contains where
  showsPrec i (Contains γ x) =
    showParen (i > 10) $
      shows γ ∘ (" ∈ " ++) ∘ shows x

instance Show IsType where
  showsPrec i (IsType α) =
    showParen (i > 10) $
      shows α ∘ (" type" ++)

derive [''Tm, ''Tele, ''Hyp, ''Chk, ''Inf, ''Equal, ''IsType, ''EqualTypes]
instance Alpha Tm
instance Alpha Tele
instance Alpha Hyp
instance Alpha Chk
instance Alpha Inf
instance Alpha Equal
instance Alpha IsType
instance Alpha EqualTypes

instance Subst Tm Tm where
  isvar m = m ^? _V . to SubstName

instance Show (Hypothetical j) where
  showsPrec i (γ :⊢ j) =
    showParen (i > 10) $
      shows γ ∘ (" ⊢ " ++) ∘ shows j
  showsPrec _ _ = error "This is total"

(⊢)
  ∷ Alpha j
  ⇒ Tele
  → j
  → Hypothetical j
γ ⊢ j = Hypothetical $ rebind j γ

infixl 8 ⊢

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

instance Judgement Contains Tm where
  judge (Empty :∋ x) = throwError $ NoSuchVariable x
  judge j@(γ :> (y :∈ α) :∋ x)
    | x == y = return α
    | otherwise = trace j ∘ judge $ γ :∋ x
  judge _ = error "This is total"

instance Judgement (Hypothetical IsType) Int where
  judge j@(_ :⊢ IsType (Univ n))
    | n ≥ 0 = return $ succ n
    | otherwise = trace j $ throwError InvalidUniverse
  judge (_ :⊢ IsType Unit) = return 0
  judge (_ :⊢ IsType Void) = return 0
  judge j@(γ :⊢ IsType (Plus α β)) =
    trace j $ max
      <$> judge (γ ⊢ IsType α)
      <*> judge (γ ⊢ IsType β)
  judge j@(γ :⊢ IsType (Pi α xβ)) =
    trace j $ do max
      <$> judge (γ ⊢ IsType α)
      <*> do
        (x, β) ← unbind xβ
        judge $ γ >: (x :∈ α) ⊢ IsType β

  judge j = trace j $ throwError NotImplemented

instance Judgement (Hypothetical Inf) Tm where
  judge j@(γ :⊢ Inf (V x)) =
    trace j ∘ judge $ γ :∋ x
  judge (_ :⊢ Inf (Univ n)) = return $ Univ (succ n)
  judge (_ :⊢ Inf Unit) = return $ Univ 0
  judge (_ :⊢ Inf Void) = return $ Univ 0
  judge (γ :⊢ Inf τ@Plus{}) =
    Univ <$> judge (γ ⊢ IsType τ)
  judge (γ :⊢ Inf τ@Pi{}) =
    Univ <$> judge (γ ⊢ IsType τ)
  judge (_ :⊢ Inf Ax) = return Unit
  judge j@(γ :⊢ Inf (App m n)) =
    trace j $ do
      τ ← judge $ γ ⊢ Inf m
      (α, xβ) ← τ ^? _Pi <?> ExpectedPiType
      judge $ γ ⊢ n :⇐ α
      (x, β) ← unbind xβ
      return ∘ eval $ subst x m β
  judge j@(γ :⊢ Inf (Decide xc m ul vr)) =
    trace j $ do
      τ ← judge $ γ ⊢ Inf m
      (α, β) ← τ ^? _Plus <?> ExpectedSumType
      (x,c) ← unbind xc
      (u,l) ← unbind ul
      judge $ γ >: (u :∈ α) ⊢ l :⇐ subst x (Inl (V u)) c
      (v,r) ← unbind vr
      judge $ γ >: (v :∈ β) ⊢ r :⇐ subst x (Inr (V v)) c
      return $ subst x m c

  judge j = trace j $ throwError NotImplemented

instance Judgement (Hypothetical Chk) () where
  judge j@(γ :⊢ Inl m :⇐ Plus α β) =
    trace j $ do
      judge $ γ ⊢ m :⇐ α
      _ ← wf ∘ judge $ γ ⊢ IsType β
      return ()
  judge j@(γ :⊢ Inr m :⇐ Plus α β) =
    trace j $ do
      judge $ γ ⊢ m :⇐ β
      _ ← wf ∘ judge $ γ ⊢ IsType α
      return ()
  judge j@(γ :⊢ m :⇐ α) =
    trace j $ do
      α' ← judge $ γ ⊢ Inf m
      _ ← wf ∘ judge $ γ ⊢ EqualTypes α α'
      return ()
  judge _ = error "This is total"

instance Judgement (Hypothetical Equal) () where
  judge j@(γ :⊢ Equal α (m,n)) =
    trace j $ do
      judge $ γ ⊢ m :⇐ α
      judge $ γ ⊢ n :⇐ α
      unless (eval m `aeq` eval n) ∘ throwError $
        NotEqual m n
  judge _ = error "This is total"

instance Judgement (Hypothetical EqualTypes) Int where
  judge j@(γ :⊢ EqualTypes α β) =
    trace j $ do
      l ← judge $ γ ⊢ IsType α
      l' ← judge $ γ ⊢ IsType β
      let l'' = max l l'
      judge $ γ ⊢ Equal (Univ l'') (α, β)
      return l''
  judge _ = error "This is total"

step
  ∷ ( Functor m
    , Fresh m
    )
  ⇒ Tm
  → MaybeT m Tm
step = \case
  Plus α β → Plus <$> step α <*> step β
  Pi α β → Pi <$> step α <*> pure β
  Ann m α → Ann <$> step m <*> step α
  Inl m → Inl <$> step m
  Inr m → Inr <$> step m
  App (Lam xm) n → do
    (x, m) ← unbind xm
    return $ subst x n m
  App m n → do
    App <$> step m <*> pure n
      <|> App <$> pure m <*> step n
  Decide _ (Inl m) ul _ → do
    (u,l) ← unbind ul
    return $ subst u m l
  Decide _ (Inr m) _ vr → do
    (v,r) ← unbind vr
    return $ subst v m r
  Decide xc m ul vr →
    Decide xc <$> step m <*> pure ul <*> pure vr
  _ → mzero

-- | Thanks to Stephanie Weirich for this nice way to do small-step CBV
-- operational semantics.
star
  ∷ Monad m
  ⇒ (α → MaybeT m α)
  → (α → m α)
star f a = do
  ma' ← runMaybeT (f a)
  case ma' of
    Just a' → star f a'
    Nothing → return a

eval
  ∷ Tm
  → Tm
eval =
  runFreshM ∘ star step

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE UnicodeSyntax #-}

module TT.Eval
( eval ) where

import Control.Applicative
import Control.Monad
import Control.Monad.Trans.Maybe
import Prelude.Unicode
import Unbound.LocallyNameless hiding (Refl)

import TT.Tm

step
  ∷ ( Functor m
    , Fresh m
    )
  ⇒ Tm
  → MaybeT m Tm
step = \case
  Plus α β → Plus <$> step α <*> step β
  Pi α β → Pi <$> step α <*> pure β
  Id α (m, n) → Id <$> step α <*> ((,) <$> step m <*> step n)
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
  IdPeel _ (Refl m) ud → do
    (u,d) ← unbind ud
    return $ subst u m d
  IdPeel xypc m ud → do
    IdPeel xypc <$> step m <*> pure ud
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

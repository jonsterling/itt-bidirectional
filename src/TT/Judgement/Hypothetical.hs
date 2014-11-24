{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE ViewPatterns #-}

module TT.Judgement.Hypothetical where

import Unbound.LocallyNameless
import Prelude.Unicode

import TT.Tele

data Hypothetical j where
  Hypothetical
    ∷ Alpha j
    ⇒ Rebind j Tele
    → Hypothetical j

infixl 8 :⊢
pattern γ :⊢ j ← Hypothetical (unrebind → (j, γ))

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

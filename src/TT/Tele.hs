{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE ViewPatterns #-}

module TT.Tele where

import TT.Hyp

import Control.Lens
import Prelude.Unicode
import Unbound.LocallyNameless

data Tele
  = Empty
  | Cons (Rebind Hyp Tele)

makePrisms ''Tele
derive [''Tele]

instance Alpha Tele

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

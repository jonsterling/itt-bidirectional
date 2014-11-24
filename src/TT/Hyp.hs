{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UnicodeSyntax #-}

module TT.Hyp where

import TT.Tm

import Prelude.Unicode
import Unbound.LocallyNameless

data Hyp
  = Hyp (Name Tm) (Embed Tm)

instance Show Hyp where
  showsPrec i (Hyp x (Embed α)) =
    showParen (i > 10) $
      shows x ∘ (" : " ++) ∘ shows α

derive [''Hyp]
instance Alpha Hyp

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}

module TT.Tm where

import Control.Lens
import Unbound.LocallyNameless hiding (Refl, to)

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
  | Id Tm (Tm, Tm)
  | Refl Tm
  | IdPeel (Bind (Name Tm, Name Tm, Name Tm) Tm) Tm (Bind (Name Tm) Tm)
  deriving Show

makePrisms ''Tm
derive [''Tm]

instance Alpha Tm

instance Subst Tm Tm where
  isvar m = m ^? _V . to SubstName


{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE UnicodeSyntax #-}

module TT.Judgement.Contains where

import Control.Monad.Error.Class
import Prelude.Unicode
import Unbound.LocallyNameless

import TT.Judgement.Class
import TT.Tele
import TT.Tm

data Contains
  = Contains Tele (Name Tm)

infixl 9 :∋
pattern γ :∋ x = Contains γ x

instance Show Contains where
  showsPrec i (Contains γ x) =
    showParen (i > 10) $
      shows γ ∘ (" ∈ " ++) ∘ shows x

instance Judgement Contains Tm where
  judge (Empty :∋ x) = throwError $ NoSuchVariable x
  judge j@(γ :> (y :∈ α) :∋ x)
    | x == y = return α
    | otherwise = trace j ∘ judge $ γ :∋ x
  judge _ = error "This is total"


{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UnicodeSyntax #-}

module TT.Judgement.Bidirectional where

import Control.Applicative
import Control.Lens
import Control.Monad
import Control.Monad.Error.Class
import Prelude.Unicode
import Unbound.LocallyNameless hiding (Equal, Refl)

import TT.Eval
import TT.Judgement.Class
import TT.Judgement.Contains
import TT.Judgement.Hypothetical
import TT.Tele
import TT.Tm

data Chk
  = Chk Tm Tm

data Inf
  = Inf Tm
  deriving Show

data Equal
  = Equal Tm (Tm, Tm)

data EqualTypes
  = EqualTypes Tm Tm

data IsType
  = IsType Tm

infixl 9 :⇐
pattern m :⇐ α = Chk m α

derive [''Chk, ''Inf, ''Equal, ''IsType, ''EqualTypes]
instance Alpha Chk
instance Alpha Inf
instance Alpha Equal
instance Alpha IsType
instance Alpha EqualTypes

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
    trace j $ max
      <$> judge (γ ⊢ IsType α)
      <*> do
        (x, β) ← unbind xβ
        judge $ γ >: (x :∈ α) ⊢ IsType β
  judge j@(γ :⊢ IsType (Id α (m, n))) =
    trace j $ do
      l ← judge $ γ ⊢ IsType α
      judge $ γ ⊢ m :⇐ α
      judge $ γ ⊢ n :⇐ α
      return l
  judge j@(γ :⊢ IsType (V x)) =
    trace j $ do
      τ ← judge $ γ :∋ x
      τ ^? _Univ <?> ExpectedUniverse
  judge j = trace j $ throwError ExpectedType

instance Judgement (Hypothetical Inf) Tm where
  judge j@(γ :⊢ Inf (V x)) =
    trace j ∘ judge $ γ :∋ x
  judge j@(γ :⊢ Inf (Ann m α)) =
    trace j $ do
      judge $ γ ⊢ m :⇐ α
      return α
  judge (_ :⊢ Inf (Univ n)) = return $ Univ (succ n)
  judge (_ :⊢ Inf Unit) = return $ Univ 0
  judge (_ :⊢ Inf Void) = return $ Univ 0
  judge (γ :⊢ Inf τ@Plus{}) =
    Univ <$> judge (γ ⊢ IsType (eval τ))
  judge (γ :⊢ Inf τ@Pi{}) =
    Univ <$> judge (γ ⊢ IsType (eval τ))
  judge (γ :⊢ Inf τ@Id{}) =
    Univ <$> judge (γ ⊢ IsType (eval τ))
  judge (_ :⊢ Inf Ax) = return Unit
  judge j@(γ :⊢ Inf (Refl m)) =
    trace j $ do
      α ← judge $ γ ⊢ Inf m
      let m' = eval m
      return $ Id (eval α) (m', m')
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
      _ ← judge $ γ >: (x :∈ τ) ⊢ IsType (eval c)
      judge $ γ >: (u :∈ α) ⊢ l :⇐ subst x (Inl (V u)) c
      (v,r) ← unbind vr
      judge $ γ >: (v :∈ β) ⊢ r :⇐ subst x (Inr (V v)) c
      return $ subst x m c
  judge j@(γ :⊢ Inf (IdPeel xypc idp ur)) =
    trace j $ do
      τ ← judge $ γ ⊢ Inf idp
      (α, (m, n)) ← τ ^? _Id <?> ExpectedIdentityType
      ((x,y,p), c) ← unbind xypc
      _ ← judge $
        let δ = γ >: (x :∈ α) >: (y :∈ α) >: (p :∈ Id α (V x, V y))
        in δ ⊢ IsType (eval c)
      (u, r) ← unbind ur
      judge $
        let cuu = subst x (V u) $ subst y (V u) $ subst p (Refl (V u)) c
        in γ >: (u :∈ α) ⊢ r :⇐ cuu
      return ∘ eval ∘ subst x m ∘ subst y n $ subst p idp c

  judge j = trace j $ throwError NotImplemented

instance Judgement (Hypothetical Chk) () where
  judge j@(γ :⊢ τ :⇐ Univ n) =
    trace j $ do
      l ← judge $ γ ⊢ IsType (eval τ)
      unless (l < succ n) $
        throwError UniverseCycle
  judge j@(γ :⊢ Inl m :⇐ Plus α β) =
    trace j $ do
      judge $ γ ⊢ m :⇐ α
      _ ← wf ∘ judge $ γ ⊢ IsType (eval β)
      return ()
  judge j@(γ :⊢ Inr m :⇐ Plus α β) =
    trace j $ do
      judge $ γ ⊢ m :⇐ β
      _ ← wf ∘ judge $ γ ⊢ IsType (eval α)
      return ()
  judge j@(γ :⊢ Lam xm :⇐ Pi α yβ) =
    trace j $ do
      (x, m) ← unbind xm
      (y, β) ← unbind yβ
      judge $ γ >: (x :∈ α) ⊢ m :⇐ subst y (V x) β
  judge j@(γ :⊢ Refl m :⇐ Id α (n, n')) =
    trace j $ do
      judge $ γ ⊢ Equal α (m, n)
      judge $ γ ⊢ Equal α (m, n')
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
      l ← judge $ γ ⊢ IsType (eval α)
      l' ← judge $ γ ⊢ IsType (eval β)
      let l'' = max l l'
      judge $ γ ⊢ Equal (Univ l'') (α, β)
      return l''
  judge _ = error "This is total"

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

instance Show IsType where
  showsPrec i (IsType α) =
    showParen (i > 10) $
      shows α ∘ (" type" ++)

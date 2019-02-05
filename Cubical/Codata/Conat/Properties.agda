{-# OPTIONS --cubical --safe --guardedness #-}
module Cubical.Codata.Conat.Properties where

open import Cubical.Data.Unit
open import Cubical.Data.Sum
open import Cubical.Data.Empty

open import Cubical.Core.Everything

open import Cubical.Codata.Conat.Base

Unwrap-prev : Conat′ -> Set
Unwrap-prev  zero   = Unit
Unwrap-prev (suc _) = Conat

unwrap-prev : (n : Conat′) -> Unwrap-prev n
unwrap-prev  zero   = _
unwrap-prev (suc x) = x

private -- tests
  𝟘 = conat zero
  one  = succ 𝟘
  two  = succ one

  succOne≡two : succ one ≡ two
  succOne≡two i = two

  predTwo≡one : unwrap-prev (force two) ≡ one
  predTwo≡one i = one

∞ : Conat
force ∞ = suc ∞

∞+1≡∞ : succ ∞ ≡ ∞
force (∞+1≡∞ _) = suc ∞

∞+2≡∞ : succ (succ ∞) ≡ ∞
∞+2≡∞ = compPath (cong succ ∞+1≡∞) ∞+1≡∞

-- TODO: plus for conat, ∞ + ∞ ≡ ∞

mutual
  record _~_ (x y : Conat) : Set where
    coinductive
    field
      force : force x ~′ force y


  _~′_ : Conat′ → Conat′ → Set
  (inl _) ~′ (inl _) = Unit
  (inr x) ~′ (inr y) = x ~ y
  _ ~′ _ = ⊥

open _~_ public

mutual
  bisim : ∀ {x y} → x ~ y → x ≡ y
  force (bisim {x} {y} eq i) = bisim′ (force eq) i

  bisim′ : ∀ {x y} → x ~′ y → x ≡ y
  bisim′ {zero} {zero} eq = refl
  bisim′ {zero} {suc x} ()
  bisim′ {suc x} {zero} ()
  bisim′ {suc x} {suc y} eq i = suc (bisim eq i)

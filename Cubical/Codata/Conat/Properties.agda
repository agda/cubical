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

record _~_ (x y : Conat) : Set
data _~′_ (x y : Conat′) : Set
_~′′_ : Conat′ → Conat′ → Set
zero  ~′′ zero  = Unit
suc x ~′′ suc y = x ~ y
-- So impossible proofs are preserved
x ~′′ y = x ≡ y

record _~_ x y where
  coinductive
  field prove : force x ~′ force y

data _~′_  x y where
  con : x ~′′ y → x ~′ y

open _~_ public

bisim : ∀ {x y} → x ~ y → x ≡ y
force (bisim eq i) = bisim′ (prove eq) i
  where
  bisim′ : ∀ {x y} → x ~′ y → x ≡ y
  bisim′ {zero} {zero}  (con tt) = refl
  bisim′ {zero} {suc x} (con p) = p
  bisim′ {suc x} {zero} (con p) = p
  bisim′ {suc x} {suc y} (con eq) i = suc (bisim eq i)

misib : ∀ {x y} → x ≡ y → x ~ y
prove (misib x≡y) = misib′ (cong force x≡y)
  where
  misib′ : ∀ {x y} → x ≡ y → x ~′ y
  misib′ {zero} {zero} p = con tt
  misib′ {zero} {suc x} p = con p
  misib′ {suc x} {zero} p = con p
  misib′ {suc x} {suc y} p = con λ where .prove → misib′ (cong pred′ p)

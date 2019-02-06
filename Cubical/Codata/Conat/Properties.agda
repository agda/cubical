{-# OPTIONS --cubical --safe --guardedness #-}
module Cubical.Codata.Conat.Properties where

open import Cubical.Data.Unit
open import Cubical.Data.Sum
open import Cubical.Data.Empty

open import Cubical.Core.Everything
open import Cubical.Foundations.Equiv

open import Cubical.Codata.Conat.Base

Unwrap-prev : Conat′ -> Set
Unwrap-prev  zero   = Unit
Unwrap-prev (suc _) = Conat

unwrap-prev : (n : Conat′) -> Unwrap-prev n
unwrap-prev  zero   = _
unwrap-prev (suc x) = x

private -- tests
  𝟘 : Conat
  force 𝟘 = zero
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

module Bisimulation where

  record _≈_ (x y : Conat) : Set
  data _≈′_ (x y : Conat′) : Set
  _≈′′_ : Conat′ → Conat′ → Set
  -- zero  ≈′′ zero  = Unit
  suc x ≈′′ suc y = x ≈ y
  -- So impossible proofs are preserved
  x ≈′′ y = x ≡ y

  record _≈_ x y where
    coinductive
    field prove : force x ≈′ force y

  data _≈′_  x y where
    con : x ≈′′ y → x ≈′ y

  open _≈_ public

  bisim : ∀ {x y} → x ≈ y → x ≡ y
  bisim′ : ∀ {x y} → x ≈′ y → x ≡ y

  bisim′ {zero} {zero}  (con p) = p
  bisim′ {zero} {suc x} (con p) = p
  bisim′ {suc x} {zero} (con p) = p
  bisim′ {suc x} {suc y} (con eq) i = suc (bisim eq i)
  force (bisim eq i) = bisim′ (prove eq) i

  misib : ∀ {x y} → x ≡ y → x ≈ y
  misib′ : ∀ {x y} → x ≡ y → x ≈′ y

  misib′ {zero} {zero} p = con p
  misib′ {zero} {suc x} p = con p
  misib′ {suc x} {zero} p = con p
  -- misib′ {suc x} {suc y} p = con λ where .prove → misib′ (cong pred′ p)
  misib′ {suc x} {suc y} p = con (misib (cong pred′′ p))
  prove (misib x≡y) = misib′ (cong force x≡y)

  iso1 : ∀ {x y} → (p : x ≈ y) → misib (bisim p) ≡ p
  iso1′ : ∀ {x y} → (p : x ≈′ y) → misib′ (bisim′ p) ≡ p

  iso1′ {zero} {zero} (con p) i = con p
  iso1′ {zero} {suc x} (con p) i = con p
  iso1′ {suc x} {zero} (con p) i = con p
  iso1′ {suc x} {suc y} p i = p
  prove (iso1 p i) = iso1′ (prove p) i

  iso2 : ∀ {x y} → (p : x ≡ y) → bisim (misib p) ≡ p
  iso2′ : ∀ {x y} → (p : x ≡ y) → bisim′ (misib′ p) ≡ p

  iso2′ {zero} {zero} p _ = p
  iso2′ {zero} {suc x} p _ = p
  iso2′ {suc x} {zero} p _ = p
  iso2′ {suc x} {suc y} p i j = suc (iso2 (cong pred′′ p) i j)
  force (iso2 p i j) = iso2′ (cong force p) i j

  path≃bisim : ∀ {x y} → (x ≡ y) ≃ (x ≈ y)
  path≃bisim = isoToEquiv misib bisim iso2 iso1

  path≡bisim : ∀ {x y} → (x ≡ y) ≡ (x ≈ y)
  path≡bisim = ua path≃bisim

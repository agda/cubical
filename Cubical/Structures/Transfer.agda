{-

Transferring properties of terms between equivalent structures

-}
module Cubical.Structures.Transfer where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.SIP
open import Cubical.Foundations.Transport
open import Cubical.Structures.Product

private
  variable
    ℓ ℓ₀ ℓ₁ ℓ₂ ℓ₂' : Level

transfer : {ℓ₂' ℓ₀ : Level} {S : Type ℓ → Type ℓ₁} {H : Type ℓ → Type ℓ₂}
  (P : ∀ X → S X → H X → Type ℓ₀)
  (α : EquivAction H) (τ : TransportStr α)
  (ι : StrEquiv S ℓ₂') (θ : UnivalentStr S ι)
  {X Y : Type ℓ} {s : S X} {t : S Y}
  (e : (X , s) ≃[ ι ] (Y , t))
  → (h : H Y) → P X s (invEq (α (e .fst)) h) → P Y t h
transfer P α τ ι θ {X} {Y} {s} {t} e h =
  subst (λ {(Z , u , h) → P Z u h})
    (sip
      (productUnivalentStr ι θ (EquivAction→StrEquiv α)  (TransportStr→UnivalentStr α τ))
      (X , s , invEq (α (e .fst)) h)
      (Y , t , h)
      (e .fst , e .snd , secEq (α (e .fst)) h))

transfer⁻ : {ℓ₂' ℓ₀ : Level} {S : Type ℓ → Type ℓ₁} {H : Type ℓ → Type ℓ₂}
  (P : ∀ X → S X → H X → Type ℓ₀)
  (α : EquivAction H) (τ : TransportStr α)
  (ι : StrEquiv S ℓ₂') (θ : UnivalentStr S ι)
  {X Y : Type ℓ} {s : S X} {t : S Y}
  (e : (X , s) ≃[ ι ] (Y , t))
  → (h : H X) → P Y t (equivFun (α (e .fst)) h) → P X s h
transfer⁻ P α τ ι θ {X} {Y} {s} {t} e h =
  subst⁻ (λ {(Z , u , h) → P Z u h})
    (sip
      (productUnivalentStr ι θ (EquivAction→StrEquiv α)  (TransportStr→UnivalentStr α τ))
      (X , s , h)
      (Y , t , equivFun (α (e .fst)) h)
      (e .fst , e .snd , refl))

{-

Product of structures S and T: X ↦ S X × T X

-}
module Cubical.Structures.Product where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Path
open import Cubical.Foundations.SIP
open import Cubical.Data.Sigma

private
  variable
    ℓ ℓ₁ ℓ₁' ℓ₂ ℓ₂' : Level

ProductStructure : (S₁ : Type ℓ → Type ℓ₁) (S₂ : Type ℓ → Type ℓ₂)
  → Type ℓ → Type (ℓ-max ℓ₁ ℓ₂)
ProductStructure S₁ S₂ X = S₁ X × S₂ X

ProductEquivStr :
  {S₁ : Type ℓ → Type ℓ₁} (ι₁ : StrEquiv S₁ ℓ₁')
  {S₂ : Type ℓ → Type ℓ₂} (ι₂ : StrEquiv S₂ ℓ₂')
  → StrEquiv (ProductStructure S₁ S₂) (ℓ-max ℓ₁' ℓ₂')
ProductEquivStr ι₁ ι₂ (X , s₁ , s₂) (Y , t₁ , t₂) f =
  (ι₁ (X , s₁) (Y , t₁) f) × (ι₂ (X , s₂) (Y , t₂) f)

productUnivalentStr :
  {S₁ : Type ℓ → Type ℓ₁} (ι₁ : StrEquiv S₁ ℓ₁') (θ₁ : UnivalentStr S₁ ι₁)
  {S₂ : Type ℓ → Type ℓ₂} (ι₂ : StrEquiv S₂ ℓ₂') (θ₂ : UnivalentStr S₂ ι₂)
  → UnivalentStr (ProductStructure S₁ S₂) (ProductEquivStr ι₁ ι₂)
productUnivalentStr {S₁ = S₁} ι₁ θ₁ {S₂} ι₂ θ₂ {X , s₁ , s₂} {Y , t₁ , t₂} e =
  compEquiv (Σ-cong-equiv (θ₁ e) (λ _ → θ₂ e)) ΣPath≃PathΣ

productEquivAction :
  {S₁ : Type ℓ → Type ℓ₁} (α₁ : EquivAction S₁)
  {S₂ : Type ℓ → Type ℓ₂} (α₂ : EquivAction S₂)
  → EquivAction (ProductStructure S₁ S₂)
productEquivAction α₁ α₂ e = Σ-cong-equiv (α₁ e) (λ _ → α₂ e)

productTransportStr :
  {S₁ : Type ℓ → Type ℓ₁} (α₁ : EquivAction S₁) (τ₁ : TransportStr α₁)
  {S₂ : Type ℓ → Type ℓ₂} (α₂ : EquivAction S₂) (τ₂ : TransportStr α₂)
  → TransportStr (productEquivAction α₁ α₂)
productTransportStr _ τ₁ _ τ₂ e (s₁ , s₂) = ΣPathP (τ₁ e s₁ , τ₂ e s₂)

{-

Product of structures S and T: X ↦ S X × T X

-}
{-# OPTIONS --cubical --no-import-sorts --safe #-}
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


ProductEquivStr : {S₁ : Type ℓ → Type ℓ₁} (ι₁ : StrEquiv S₁ ℓ₁')
           {S₂ : Type ℓ → Type ℓ₂} (ι₂ : StrEquiv S₂ ℓ₂')
         → StrEquiv (ProductStructure S₁ S₂) (ℓ-max ℓ₁' ℓ₂')
ProductEquivStr ι₁ ι₂ (X , s₁ , s₂) (Y , t₁ , t₂) f = (ι₁ (X , s₁) (Y , t₁) f) × (ι₂ (X , s₂) (Y , t₂) f)


ProductUnivalentStr : {S₁ : Type ℓ → Type ℓ₁} (ι₁ : StrEquiv S₁ ℓ₁') (θ₁ : UnivalentStr S₁ ι₁)
           {S₂ : Type ℓ → Type ℓ₂} (ι₂ : StrEquiv S₂ ℓ₂') (θ₂ : UnivalentStr S₂ ι₂)
         → UnivalentStr (ProductStructure S₁ S₂) (ProductEquivStr ι₁ ι₂)
ProductUnivalentStr {S₁ = S₁} ι₁ θ₁ {S₂} ι₂ θ₂ {X , s₁ , s₂} {Y , t₁ , t₂} e =
  isoToEquiv (iso φ ψ η ε)
    where
    φ : ProductEquivStr ι₁ ι₂ (X , s₁ , s₂) (Y , t₁ , t₂) e
      → PathP (λ i → ProductStructure S₁ S₂ (ua e i)) (s₁ , s₂) (t₁ , t₂)
    φ (p , q) i = (θ₁ e .fst p i) , (θ₂ e .fst q i)

    ψ : PathP (λ i → ProductStructure S₁ S₂ (ua e i)) (s₁ , s₂) (t₁ , t₂)
      → ProductEquivStr ι₁ ι₂ (X , s₁ , s₂) (Y , t₁ , t₂) e
    ψ p = invEq (θ₁ e) (λ i → p i .fst) , invEq (θ₂ e) (λ i → p i .snd)

    η : section φ ψ
    η p i j = retEq (θ₁ e) (λ k → p k .fst) i j , retEq (θ₂ e) (λ k → p k .snd) i j

    ε : retract φ ψ
    ε (p , q) i = secEq (θ₁ e) p i , secEq (θ₂ e) q i

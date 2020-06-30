{-

Functions between structures S and T: X ↦ S X → T X

-}
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Structures.Function where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.SIP
open import Cubical.Foundations.Univalence

open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Nat
open import Cubical.Data.Vec

private
  variable
    ℓ ℓ₁ ℓ₁' ℓ₂ ℓ₂' : Level

-- General function structure

FunctionStructure : (S : Type ℓ → Type ℓ₁) (T : Type ℓ → Type ℓ₂)
  → Type ℓ → Type (ℓ-max ℓ₁ ℓ₂)
FunctionStructure S T X = S X → T X

FunctionEquivStr : {S : Type ℓ → Type ℓ₁} {T : Type ℓ → Type ℓ₂}
  → StrEquiv S ℓ₁' → StrEquiv T ℓ₂'
  → StrEquiv (FunctionStructure S T) (ℓ-max ℓ₁ (ℓ-max ℓ₁' ℓ₂'))
FunctionEquivStr {S = S} {T} ι₁ ι₂ (X , f) (Y , g) e =
  {s : S X} {t : S Y} → ι₁ (X , s) (Y , t) e → ι₂ (X , f s) (Y , g t) e

functionUnivalentStr : {S : Type ℓ → Type ℓ₁} {T : Type ℓ → Type ℓ₂}
  (ι₁ : StrEquiv S ℓ₁') (θ₁ : UnivalentStr S ι₁)
  (ι₂ : StrEquiv T ℓ₂') (θ₂ : UnivalentStr T ι₂)
  → UnivalentStr (FunctionStructure S T) (FunctionEquivStr ι₁ ι₂)
functionUnivalentStr ι₁ θ₁ ι₂ θ₂ e =
  compEquiv
    (equivImplicitΠCod (equivImplicitΠCod (equiv→ (θ₁ e) (θ₂ e))))
    funExtDepEquiv

-- Simpler definition of structured equivalence when the domain is functorial

FunctionEquivStr+ : {S : Type ℓ → Type ℓ₁} {T : Type ℓ → Type ℓ₂}
  → (∀ {X Y} → (X → Y) → S X → S Y) → StrEquiv T ℓ₂'
  → StrEquiv (FunctionStructure S T) (ℓ-max ℓ₁ ℓ₂')
FunctionEquivStr+ {S = S} {T} F ι₂ (X , f) (Y , g) e =
  (s : S X) → ι₂ (X , f s) (Y , g (F (e .fst) s)) e

functionUnivalentStr+ : {S : Type ℓ → Type ℓ₁} {T : Type ℓ → Type ℓ₂}
  (F : ∀ {X Y} → (X → Y) → S X → S Y) (η : ∀ {X} s → F (idfun X) s ≡ s)
  (ι₂ : StrEquiv T ℓ₂') (θ₂ : UnivalentStr T ι₂)
  → UnivalentStr (FunctionStructure S T) (FunctionEquivStr+ F ι₂)
functionUnivalentStr+ {S = S} F η ι₂ θ₂ =
  SNS→UnivalentStr
    (FunctionEquivStr+ F ι₂)
    (λ {X} t t' →
      compEquiv
        (equivΠCod λ s →
          compEquiv
            (UnivalentStr→SNS _ ι₂ θ₂ (t s) (t' (F (idfun _) s)))
            (pathToEquiv λ i → t s ≡ t' (η s i)))
        funExtEquiv)

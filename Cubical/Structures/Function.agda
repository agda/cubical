{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Structures.Function where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.SIP

open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Nat
open import Cubical.Data.Vec

private
  variable
    ℓ ℓ₁ ℓ₁' ℓ₂ ℓ₂' : Level

FunctionStructure : (S : Type ℓ → Type ℓ₁) (T : Type ℓ → Type ℓ₂)
  → Type ℓ → Type (ℓ-max ℓ₁ ℓ₂)
FunctionStructure S T X = S X → T X

FunctionEquivStr : {S : Type ℓ → Type ℓ₁} {T : Type ℓ → Type ℓ₂}
  → StrEquiv S ℓ₁' → StrEquiv T ℓ₂'
  → StrEquiv (FunctionStructure S T) (ℓ-max ℓ₁ (ℓ-max ℓ₁' ℓ₂'))
FunctionEquivStr {S = S} {T} ι₁ ι₂ (X , f) (Y , g) e =
  {s : S X} {t : S Y} → ι₁ (X , s) (Y , t) e → ι₂ (X , f s) (Y , g t) e 

FunctionUnivalentStr : {S : Type ℓ → Type ℓ₁} {T : Type ℓ → Type ℓ₂}
  (ι₁ : StrEquiv S ℓ₁') (θ₁ : UnivalentStr S ι₁)
  (ι₂ : StrEquiv T ℓ₂') (θ₂ : UnivalentStr T ι₂)
  → UnivalentStr (FunctionStructure S T) (FunctionEquivStr ι₁ ι₂)
FunctionUnivalentStr ι₁ θ₁ ι₂ θ₂ e =
  compEquiv
    (equivImplicitΠCod (equivImplicitΠCod (equiv→ (θ₁ e) (θ₂ e))))
    funExtDepEquiv

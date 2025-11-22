{-

Functions between structures S and T: X ↦ S X → T X

-}
module Cubical.Structures.Function where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path
open import Cubical.Foundations.SIP
open import Cubical.Foundations.Transport
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

functionEquivAction : {S : Type ℓ → Type ℓ₁} {T : Type ℓ → Type ℓ₂}
  → EquivAction S → EquivAction T
  → EquivAction (FunctionStructure S T)
functionEquivAction α₁ α₂ e = equiv→ (α₁ e) (α₂ e)

functionTransportStr : {S : Type ℓ → Type ℓ₁} {T : Type ℓ → Type ℓ₂}
  (α₁ : EquivAction S) (τ₁ : TransportStr α₁)
  (α₂ : EquivAction T) (τ₂ : TransportStr α₂)
  → TransportStr (functionEquivAction α₁ α₂)
functionTransportStr {S = S} α₁ τ₁ α₂ τ₂ e f =
  funExt λ t →
  cong (equivFun (α₂ e) ∘ f) (invTransportStr α₁ τ₁ e t)
  ∙ τ₂ e (f (subst⁻ S (ua e) t))

-- Definition of structured equivalence using an action in the domain

FunctionEquivStr+ : {S : Type ℓ → Type ℓ₁} {T : Type ℓ → Type ℓ₂}
  → EquivAction S → StrEquiv T ℓ₂'
  → StrEquiv (FunctionStructure S T) (ℓ-max ℓ₁ ℓ₂')
FunctionEquivStr+ {S = S} {T} α₁ ι₂ (X , f) (Y , g) e =
  (s : S X) → ι₂ (X , f s) (Y , g (equivFun (α₁ e) s)) e

functionUnivalentStr+ : {S : Type ℓ → Type ℓ₁} {T : Type ℓ → Type ℓ₂}
  (α₁ : EquivAction S) (τ₁ : TransportStr α₁)
  (ι₂ : StrEquiv T ℓ₂') (θ₂ : UnivalentStr T ι₂)
  → UnivalentStr (FunctionStructure S T) (FunctionEquivStr+ α₁ ι₂)
functionUnivalentStr+ {S = S} {T} α₁ τ₁ ι₂ θ₂ {X , f} {Y , g} e =
  compEquiv
    (compEquiv
      (equivΠCod λ s →
        compEquiv
          (θ₂ e)
          (pathToEquiv (cong (PathP (λ i → T (ua e i)) (f s) ∘ g) (τ₁ e s))))
      (invEquiv heteroHomotopy≃Homotopy))
    funExtDepEquiv

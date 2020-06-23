{-

A parameterized family of structures can be combined into a single structure

-}
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Structures.Parameterized where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Functions.FunExtEquiv
open import Cubical.Foundations.SIP

module _ {ℓ ℓ₁ ℓ₂} (A : Type ℓ) where

  ParamStructure : (S : A → Type ℓ₁ → Type ℓ₂)
    → Type ℓ₁ → Type (ℓ-max ℓ ℓ₂)
  ParamStructure S X = (a : A) → S a X

  ParamEquivStr : {S : A → Type ℓ₁ → Type ℓ₂} {ℓ₃ : Level}
    → (∀ a → StrEquiv (S a) ℓ₃) → StrEquiv (ParamStructure S) (ℓ-max ℓ ℓ₃)
  ParamEquivStr ι (X , l) (Y , m) e = ∀ a → ι a (X , l a) (Y , m a) e

  ParamUnivalentStr : {S : A → Type ℓ₁ → Type ℓ₂} {ℓ₃ : Level}
    (ι : ∀ a → StrEquiv (S a) ℓ₃) (θ : ∀ a → UnivalentStr (S a) (ι a))
    → UnivalentStr (ParamStructure S) (ParamEquivStr ι)
  ParamUnivalentStr ι θ e = compEquiv (equivPi λ a → θ a e) funExtEquiv

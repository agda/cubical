{-

A parameterized family of structures can be combined into a single structure

-}
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Structures.Parameterized where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Functions.FunExtEquiv
open import Cubical.Foundations.SIP renaming (SNS-PathP to SNS)

module _ {ℓ ℓ₁ ℓ₂} (A : Type ℓ) where

  parameterized-structure : (S : A → Type ℓ₁ → Type ℓ₂)
    → Type ℓ₁ → Type (ℓ-max ℓ ℓ₂)
  parameterized-structure S X = (a : A) → S a X

  parameterized-iso : {S : A → Type ℓ₁ → Type ℓ₂} {ℓ₃ : Level}
    → (∀ a → StrIso (S a) ℓ₃) → StrIso (parameterized-structure S) (ℓ-max ℓ ℓ₃)
  parameterized-iso ι (X , l) (Y , m) e = ∀ a → ι a (X , l a) (Y , m a) e

  Parameterized-is-SNS : {S : A → Type ℓ₁ → Type ℓ₂} {ℓ₃ : Level}
    (ι : ∀ a → StrIso (S a) ℓ₃) (θ : ∀ a → SNS (S a) (ι a))
    → SNS (parameterized-structure S) (parameterized-iso ι)
  Parameterized-is-SNS ι θ e = compEquiv (equivPi λ a → θ a e) funExtEquiv

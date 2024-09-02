{-# OPTIONS --safe #-}

module Cubical.HITs.SphereBouquet.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed

open import Cubical.Data.Nat

open import Cubical.HITs.Wedge
open import Cubical.HITs.Sn

SphereBouquet : ∀ {ℓ} (n : ℕ) (A : Type ℓ) → Type ℓ
SphereBouquet n A = ⋁gen A λ a → S₊∙ n

SphereBouquet∙ : ∀ {ℓ} (n : ℕ) (A : Type ℓ) → Pointed ℓ
SphereBouquet∙ n A = ⋁gen∙ A λ a → S₊∙ n

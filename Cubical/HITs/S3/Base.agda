{-# OPTIONS --safe #-}
module Cubical.HITs.S3.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open Iso

data S³ : Type₀ where
  base : S³
  surf : PathP (λ j → PathP (λ i → base ≡ base) refl refl) refl refl

flip₀₂S³ : S³ → S³
flip₀₂S³ base = base
flip₀₂S³ (surf j i i₁) = surf i₁ i j

flip₀₂S³Id : (x : S³) → flip₀₂S³ (flip₀₂S³ x) ≡ x
flip₀₂S³Id base = refl
flip₀₂S³Id (surf j i i₁) = refl

flip₀₂S³Iso : Iso S³ S³
fun flip₀₂S³Iso = flip₀₂S³
inv flip₀₂S³Iso = flip₀₂S³
rightInv flip₀₂S³Iso = flip₀₂S³Id
leftInv flip₀₂S³Iso = flip₀₂S³Id

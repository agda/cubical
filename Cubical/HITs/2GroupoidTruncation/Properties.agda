{-

This file contains:

- Properties of 2-groupoid truncations

-}
{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.2GroupoidTruncation.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.HITs.2GroupoidTruncation.Base

rec : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (gB : is2Groupoid B) → (A → B) → (∥ A ∥₂ → B)
rec gB f ∣ x ∣₂ = f x
rec gB f (squash₂ _ _ _ _ _ _ t u i j k l) =
  gB _ _ _ _ _ _
    (λ m n o → rec gB f (t m n o))
    (λ m n o → rec gB f (u m n o))
    i j k l

elim : ∀ {ℓ ℓ'} {A : Type ℓ} {B : ∥ A ∥₂ → Type ℓ'}
  (bG : (x : ∥ A ∥₂) → is2Groupoid (B x))
  (f : (x : A) → B ∣ x ∣₂) (x : ∥ A ∥₂) → B x
elim bG f ∣ x ∣₂ = f x
elim bG f (squash₂ x y p q r s u v i j k l) =
  isOfHLevel→isOfHLevelDep 4 bG _ _ _ _ _ _
    (λ j k l → elim bG f (u j k l)) (λ j k l → elim bG f (v j k l))
    (squash₂ x y p q r s u v)
    i j k l

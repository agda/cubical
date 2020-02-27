{-

This file contains:

- Properties of groupoid truncations

-}
{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.GroupoidTruncation.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.HITs.GroupoidTruncation.Base

rec : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (gB : isGroupoid B) → (A → B) → (∥ A ∥₁ → B)
rec gB f ∣ x ∣₁ = f x
rec gB f (squash₁ x y p q r s i j k) =
  gB _ _ _ _
    (λ m n → rec gB f (r m n))
    (λ m n → rec gB f (s m n))
    i j k

elim : ∀ {ℓ ℓ'} {A : Type ℓ} {B : ∥ A ∥₁ → Type ℓ'}
  (bG : (x : ∥ A ∥₁) → isGroupoid (B x))
  (f : (x : A) → B ∣ x ∣₁) (x : ∥ A ∥₁) → B x
elim bG f (∣ x ∣₁) = f x
elim bG f (squash₁ x y p q r s i j k) =
  isOfHLevel→isOfHLevelDep 3 bG
    (elim bG f x) (elim bG f y)
    (cong (elim bG f) p) (cong (elim bG f) q)
    (λ j k → elim bG f (r j k)) (λ j k → elim bG f (s j k))
    (squash₁ x y p q r s)
    i j k

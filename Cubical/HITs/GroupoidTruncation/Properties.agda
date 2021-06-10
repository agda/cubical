{-

This file contains:

- Properties of groupoid truncations

-}
{-# OPTIONS --safe #-}
module Cubical.HITs.GroupoidTruncation.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence

open import Cubical.HITs.GroupoidTruncation.Base

private
  variable
    ℓ : Level
    A : Type ℓ

rec : ∀ {B : Type ℓ} → isGroupoid B → (A → B) → ∥ A ∥₃ → B
rec gB f ∣ x ∣₃ = f x
rec gB f (squash₃ x y p q r s i j k) =
  gB _ _ _ _ (λ m n → rec gB f (r m n)) (λ m n → rec gB f (s m n)) i j k

elim : {B : ∥ A ∥₃ → Type ℓ}
       (bG : (x : ∥ A ∥₃) → isGroupoid (B x))
       (f : (x : A) → B ∣ x ∣₃) (x : ∥ A ∥₃) → B x
elim bG f (∣ x ∣₃) = f x
elim bG f (squash₃ x y p q r s i j k) =
  isOfHLevel→isOfHLevelDep 3 bG _ _ _ _
    (λ j k → elim bG f (r j k)) (λ j k → elim bG f (s j k))
    (squash₃ x y p q r s)
    i j k

elim2 : {B : ∥ A ∥₃ → ∥ A ∥₃ → Type ℓ}
        (gB : ((x y : ∥ A ∥₃) → isGroupoid (B x y)))
        (g : (a b : A) → B ∣ a ∣₃ ∣ b ∣₃)
        (x y : ∥ A ∥₃) → B x y
elim2 gB g = elim (λ _ → isGroupoidΠ (λ _ → gB _ _))
                  (λ a → elim (λ _ → gB _ _) (g a))

elim3 : {B : (x y z : ∥ A ∥₃) → Type ℓ}
        (gB : ((x y z : ∥ A ∥₃) → isGroupoid (B x y z)))
        (g : (a b c : A) → B ∣ a ∣₃ ∣ b ∣₃ ∣ c ∣₃)
        (x y z : ∥ A ∥₃) → B x y z
elim3 gB g = elim2 (λ _ _ → isGroupoidΠ (λ _ → gB _ _ _))
                   (λ a b → elim (λ _ → gB _ _ _) (g a b))

isGroupoidGroupoidTrunc : isGroupoid ∥ A ∥₃
isGroupoidGroupoidTrunc a b p q r s = squash₃ a b p q r s

groupoidTruncIdempotent≃ : isGroupoid A → ∥ A ∥₃ ≃ A
groupoidTruncIdempotent≃ {A = A} hA = isoToEquiv f
  where
  f : Iso ∥ A ∥₃ A
  Iso.fun f = rec hA (idfun A)
  Iso.inv f x = ∣ x ∣₃
  Iso.rightInv f _ = refl
  Iso.leftInv f = elim (λ _ → isGroupoid→is2Groupoid isGroupoidGroupoidTrunc _ _) (λ _ → refl)

groupoidTruncIdempotent : isGroupoid A → ∥ A ∥₃ ≡ A
groupoidTruncIdempotent hA = ua (groupoidTruncIdempotent≃ hA)

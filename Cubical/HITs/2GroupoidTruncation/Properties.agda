{-

This file contains:

- Properties of 2-groupoid truncations

-}
{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.2GroupoidTruncation.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence

open import Cubical.HITs.2GroupoidTruncation.Base

private
  variable
    ℓ : Level
    A : Type ℓ

rec : ∀ {B : Type ℓ} → is2Groupoid B → (A → B) → ∥ A ∥₂ → B
rec gB f ∣ x ∣₂ = f x
rec gB f (squash₂ _ _ _ _ _ _ t u i j k l) =
  gB _ _ _ _ _ _ (λ m n o → rec gB f (t m n o)) (λ m n o → rec gB f (u m n o))
     i j k l

elim : {B : ∥ A ∥₂ → Type ℓ}
       (bG : (x : ∥ A ∥₂) → is2Groupoid (B x))
       (f : (x : A) → B ∣ x ∣₂) (x : ∥ A ∥₂) → B x
elim bG f ∣ x ∣₂ = f x
elim bG f (squash₂ x y p q r s u v i j k l) =
  isOfHLevel→isOfHLevelDep 4 bG _ _ _ _ _ _
    (λ j k l → elim bG f (u j k l)) (λ j k l → elim bG f (v j k l))
    (squash₂ x y p q r s u v)
    i j k l

elim2 : {B : ∥ A ∥₂ → ∥ A ∥₂ → Type ℓ}
        (gB : ((x y : ∥ A ∥₂) → is2Groupoid (B x y)))
        (g : (a b : A) → B ∣ a ∣₂ ∣ b ∣₂)
        (x y : ∥ A ∥₂) → B x y
elim2 gB g = elim (λ _ → is2GroupoidΠ (λ _ → gB _ _))
                  (λ a → elim (λ _ → gB _ _) (g a))

elim3 : {B : (x y z : ∥ A ∥₂) → Type ℓ}
        (gB : ((x y z : ∥ A ∥₂) → is2Groupoid (B x y z)))
        (g : (a b c : A) → B ∣ a ∣₂ ∣ b ∣₂ ∣ c ∣₂)
        (x y z : ∥ A ∥₂) → B x y z
elim3 gB g = elim2 (λ _ _ → is2GroupoidΠ (λ _ → gB _ _ _))
                   (λ a b → elim (λ _ → gB _ _ _) (g a b))

2GroupoidTruncIs2Groupoid : is2Groupoid ∥ A ∥₂
2GroupoidTruncIs2Groupoid a b p q r s = squash₂ a b p q r s

2GroupoidTruncIdempotent≃ : is2Groupoid A → ∥ A ∥₂ ≃ A
2GroupoidTruncIdempotent≃ {A = A} hA = isoToEquiv f
  where
  f : Iso ∥ A ∥₂ A
  Iso.fun f = rec hA (idfun A)
  Iso.inv f x = ∣ x ∣₂
  Iso.rightInv f _ = refl
  Iso.leftInv f = elim (λ _ → isOfHLevelSuc 4 2GroupoidTruncIs2Groupoid _ _) (λ _ → refl)

2GroupoidTruncIdempotent : is2Groupoid A → ∥ A ∥₂ ≡ A
2GroupoidTruncIdempotent hA = ua (2GroupoidTruncIdempotent≃ hA)

{-

This file contains:

- Properties of 2-groupoid truncations

-}
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

rec : ∀ {B : Type ℓ} → is2Groupoid B → (A → B) → ∥ A ∥₄ → B
rec gB f ∣ x ∣₄ = f x
rec gB f (squash₄ _ _ _ _ _ _ t u i j k l) =
  gB _ _ _ _ _ _ (λ m n o → rec gB f (t m n o)) (λ m n o → rec gB f (u m n o))
     i j k l

elim : {B : ∥ A ∥₄ → Type ℓ}
       (bG : (x : ∥ A ∥₄) → is2Groupoid (B x))
       (f : (x : A) → B ∣ x ∣₄) (x : ∥ A ∥₄) → B x
elim bG f ∣ x ∣₄ = f x
elim bG f (squash₄ x y p q r s u v i j k l) =
  isOfHLevel→isOfHLevelDep 4 bG _ _ _ _ _ _
    (λ j k l → elim bG f (u j k l)) (λ j k l → elim bG f (v j k l))
    (squash₄ x y p q r s u v)
    i j k l

elim2 : {B : ∥ A ∥₄ → ∥ A ∥₄ → Type ℓ}
        (gB : ((x y : ∥ A ∥₄) → is2Groupoid (B x y)))
        (g : (a b : A) → B ∣ a ∣₄ ∣ b ∣₄)
        (x y : ∥ A ∥₄) → B x y
elim2 gB g = elim (λ _ → is2GroupoidΠ (λ _ → gB _ _))
                  (λ a → elim (λ _ → gB _ _) (g a))

elim3 : {B : (x y z : ∥ A ∥₄) → Type ℓ}
        (gB : ((x y z : ∥ A ∥₄) → is2Groupoid (B x y z)))
        (g : (a b c : A) → B ∣ a ∣₄ ∣ b ∣₄ ∣ c ∣₄)
        (x y z : ∥ A ∥₄) → B x y z
elim3 gB g = elim2 (λ _ _ → is2GroupoidΠ (λ _ → gB _ _ _))
                   (λ a b → elim (λ _ → gB _ _ _) (g a b))

is2Groupoid2GroupoidTrunc : is2Groupoid ∥ A ∥₄
is2Groupoid2GroupoidTrunc a b p q r s = squash₄ a b p q r s

2GroupoidTruncIdempotent≃ : is2Groupoid A → ∥ A ∥₄ ≃ A
2GroupoidTruncIdempotent≃ {A = A} hA = isoToEquiv f
  where
  f : Iso ∥ A ∥₄ A
  Iso.fun f = rec hA (idfun A)
  Iso.inv f x = ∣ x ∣₄
  Iso.rightInv f _ = refl
  Iso.leftInv f = elim (λ _ → isOfHLevelSuc 4 is2Groupoid2GroupoidTrunc _ _) (λ _ → refl)

2GroupoidTruncIdempotent : is2Groupoid A → ∥ A ∥₄ ≡ A
2GroupoidTruncIdempotent hA = ua (2GroupoidTruncIdempotent≃ hA)

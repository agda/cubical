{-

This file contains:

- Properties of set truncations

-}
{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.SetTruncation.Properties where

open import Cubical.HITs.SetTruncation.Base

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence

private
  variable
    ℓ : Level
    A : Type ℓ

rec : {B : Type ℓ} → isSet B → (A → B) → ∥ A ∥₂ → B
rec Bset f ∣ x ∣₂ = f x
rec Bset f (squash₂ x y p q i j) =
  Bset _ _ (cong (rec Bset f) p) (cong (rec Bset f) q) i j

-- lemma 6.9.1 in HoTT book
elim : {B : ∥ A ∥₂ → Type ℓ}
       (Bset : (x : ∥ A ∥₂) → isSet (B x))
       (g : (a : A) → B (∣ a ∣₂))
       (x : ∥ A ∥₂) → B x
elim Bset g ∣ a ∣₂ = g a
elim Bset g (squash₂ x y p q i j) =
  isOfHLevel→isOfHLevelDep 2 Bset _ _
    (cong (elim Bset g) p) (cong (elim Bset g) q) (squash₂ x y p q) i j

setTruncUniversal : {B : Type ℓ} → isSet B → (∥ A ∥₂ → B) ≃ (A → B)
setTruncUniversal {B = B} Bset =
  isoToEquiv (iso (λ h x → h ∣ x ∣₂) (rec Bset) (λ _ → refl) rinv)
  where
  rinv : (f : ∥ A ∥₂ → B) → rec Bset (λ x → f ∣ x ∣₂) ≡ f
  rinv f i x =
    elim (λ x → isProp→isSet (Bset (rec Bset (λ x → f ∣ x ∣₂) x) (f x)))
         (λ _ → refl) x i

elim2 : {B : ∥ A ∥₂ → ∥ A ∥₂ → Type ℓ}
        (Bset : ((x y : ∥ A ∥₂) → isSet (B x y)))
        (g : (a b : A) → B ∣ a ∣₂ ∣ b ∣₂)
        (x y : ∥ A ∥₂) → B x y
elim2 Bset g = elim (λ _ → isSetΠ (λ _ → Bset _ _))
                    (λ a → elim (λ _ → Bset _ _) (g a))

elim3 : {B : (x y z : ∥ A ∥₂) → Type ℓ}
        (Bset : ((x y z : ∥ A ∥₂) → isSet (B x y z)))
        (g : (a b c : A) → B ∣ a ∣₂ ∣ b ∣₂ ∣ c ∣₂)
        (x y z : ∥ A ∥₂) → B x y z
elim3 Bset g = elim2 (λ _ _ → isSetΠ (λ _ → Bset _ _ _))
                     (λ a b → elim (λ _ → Bset _ _ _) (g a b))

setTruncIsSet : isSet ∥ A ∥₂
setTruncIsSet a b p q = squash₂ a b p q

setTruncIdempotent≃ : isSet A → ∥ A ∥₂ ≃ A
setTruncIdempotent≃ {A = A} hA = isoToEquiv f
  where
  f : Iso ∥ A ∥₂ A
  Iso.fun f = rec hA (idfun A)
  Iso.inv f x = ∣ x ∣₂
  Iso.rightInv f _ = refl
  Iso.leftInv f = elim (λ _ → isSet→isGroupoid setTruncIsSet _ _) (λ _ → refl)

setTruncIdempotent : isSet A → ∥ A ∥₂ ≡ A
setTruncIdempotent hA = ua (setTruncIdempotent≃ hA)

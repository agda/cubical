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
open import Cubical.Data.Sigma

private
  variable
    ℓ : Level
    A : Type ℓ

rec : {B : Type ℓ} → isSet B → (A → B) → ∥ A ∥₀ → B
rec Bset f ∣ x ∣₀ = f x
rec Bset f (squash₀ x y p q i j) =
  Bset _ _ (cong (rec Bset f) p) (cong (rec Bset f) q) i j

-- lemma 6.9.1 in HoTT book
elim : {B : ∥ A ∥₀ → Type ℓ}
       (Bset : (x : ∥ A ∥₀) → isSet (B x))
       (g : (a : A) → B (∣ a ∣₀))
       (x : ∥ A ∥₀) → B x
elim Bset g ∣ a ∣₀ = g a
elim Bset g (squash₀ x y p q i j) =
  isOfHLevel→isOfHLevelDep 2 Bset _ _
    (cong (elim Bset g) p) (cong (elim Bset g) q) (squash₀ x y p q) i j

setTruncUniversal : {B : Type ℓ} → isSet B → (∥ A ∥₀ → B) ≃ (A → B)
setTruncUniversal {B = B} Bset =
  isoToEquiv (iso (λ h x → h ∣ x ∣₀) (rec Bset) (λ _ → refl) rinv)
  where
  rinv : (f : ∥ A ∥₀ → B) → rec Bset (λ x → f ∣ x ∣₀) ≡ f
  rinv f i x =
    elim (λ x → isProp→isSet (Bset (rec Bset (λ x → f ∣ x ∣₀) x) (f x)))
         (λ _ → refl) x i

elim2 : {B : ∥ A ∥₀ → ∥ A ∥₀ → Type ℓ}
        (Bset : ((x y : ∥ A ∥₀) → isSet (B x y)))
        (g : (a b : A) → B ∣ a ∣₀ ∣ b ∣₀)
        (x y : ∥ A ∥₀) → B x y
elim2 Bset g = elim (λ _ → isSetΠ (λ _ → Bset _ _))
                    (λ a → elim (λ _ → Bset _ _) (g a))

elim3 : {B : (x y z : ∥ A ∥₀) → Type ℓ}
        (Bset : ((x y z : ∥ A ∥₀) → isSet (B x y z)))
        (g : (a b c : A) → B ∣ a ∣₀ ∣ b ∣₀ ∣ c ∣₀)
        (x y z : ∥ A ∥₀) → B x y z
elim3 Bset g = elim2 (λ _ _ → isSetΠ (λ _ → Bset _ _ _))
                     (λ a b → elim (λ _ → Bset _ _ _) (g a b))

setTruncIsSet : isSet ∥ A ∥₀
setTruncIsSet a b p q = squash₀ a b p q

setTruncIdempotent≃ : isSet A → ∥ A ∥₀ ≃ A
setTruncIdempotent≃ {A = A} hA = isoToEquiv f
  where
  f : Iso ∥ A ∥₀ A
  Iso.fun f = rec hA (idfun A)
  Iso.inv f x = ∣ x ∣₀
  Iso.rightInv f _ = refl
  Iso.leftInv f = elim (λ _ → isSet→isGroupoid setTruncIsSet _ _) (λ _ → refl)

setTruncIdempotent : isSet A → ∥ A ∥₀ ≡ A
setTruncIdempotent hA = ua (setTruncIdempotent≃ hA)


setSigmaIso : ∀ {ℓ} {B : A → Type ℓ} → Iso ∥ Σ A B ∥₀ ∥ Σ A (λ x → ∥ B x ∥₀) ∥₀
setSigmaIso {A = A} {B = B} = iso fun funinv sect retr
  where
  {- writing it out explicitly to avoid yellow highlighting -}
  fun : ∥ Σ A B ∥₀ → ∥ Σ A (λ x → ∥ B x ∥₀) ∥₀
  fun = rec setTruncIsSet λ {(a , p) → ∣ a , ∣ p ∣₀ ∣₀}
  funinv : ∥ Σ A (λ x → ∥ B x ∥₀) ∥₀ → ∥ Σ A B ∥₀
  funinv = rec setTruncIsSet (λ {(a , p) → rec setTruncIsSet (λ p → ∣ a , p ∣₀) p})
  sect : section fun funinv
  sect = elim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
              λ { (a , p) → elim {B = λ p → fun (funinv ∣ a , p ∣₀) ≡ ∣ a , p ∣₀}
              (λ p → isOfHLevelPath 2 setTruncIsSet _ _) (λ _ → refl) p }
  retr : retract fun funinv
  retr = elim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
              λ { _ → refl }

{-

This file contains:

- Properties of set truncations

-}
{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.SetTruncation.Properties where

open import Cubical.HITs.SetTruncation.Base

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels

private
  variable
    ℓ : Level
    A : Type ℓ

-- lemma 6.9.1 in HoTT book
elim : {B : ∥ A ∥₀ → Type ℓ} →
  (Bset : (x : ∥ A ∥₀) → isSet (B x)) →
  (g : (a : A) → B (∣ a ∣₀)) →
  (x : ∥ A ∥₀) → B x
elim Bset g ∣ a ∣₀ = g a
elim {A = A} {B = B} Bset g (squash₀ x y p q i j) =
  isOfHLevel→isOfHLevelDep 2 Bset  (elim Bset g x) (elim Bset g y)
    (cong (elim Bset g) p) (cong (elim Bset g) q) (squash₀ x y p q) i j

setTruncUniversal : {B : Type ℓ} → (isSet B) → (∥ A ∥₀ → B) ≃ (A → B)
setTruncUniversal Bset = isoToEquiv (iso intro out leftInv rightInv)
  where
  intro = (λ h a → h ∣ a ∣₀)
  out = elim (λ x → Bset)

  leftInv : ∀ g → intro (out g) ≡ g
  leftInv g = refl

  rightInv : ∀ h → out (intro h) ≡ h
  rightInv h i x = elim (λ x → isProp→isSet (Bset (out (intro h) x) (h x)))
                                (λ a → refl) x i

elim2 : {B : ∥ A ∥₀ → ∥ A ∥₀ → Type ℓ}
  (Bset : ((x y : ∥ A ∥₀) → isSet (B x y)))
  (g : (a b : A) → B ∣ a ∣₀ ∣ b ∣₀)
  (x y : ∥ A ∥₀) → B x y
elim2 Bset g = elim (λ _ → hLevelPi 2 (λ _ → Bset _ _)) (λ a →
                       elim (λ _ → Bset _ _) (λ b → g a b))

elim3 : {B : (x y z : ∥ A ∥₀) → Type ℓ}
  (Bset : ((x y z : ∥ A ∥₀) → isSet (B x y z)))
  (g : (a b c : A) → B ∣ a ∣₀ ∣ b ∣₀ ∣ c ∣₀)
  (x y z : ∥ A ∥₀) → B x y z
elim3 Bset g = elim2 (λ _ _ → hLevelPi 2 λ _ → Bset _ _ _) (λ a b →
                       elim (λ _ → Bset _ _ _) (λ c → g a b c))

setTruncIsSet : isSet ∥ A ∥₀
setTruncIsSet a b p q = squash₀ a b p q

setId : isSet A → ∥ A ∥₀ ≡ A
setId {A = A} isset =
  isoToPath (iso (elim {A = A} (λ _ → isset) (λ x → x)) (λ x → ∣ x ∣₀) (λ b → refl) (λ b → idLemma b))
  where
  idLemma : ∀ (b : ∥ A ∥₀) → ∣ elim (λ x → isset) (λ x → x) b ∣₀ ≡ b
  idLemma b =
    elim {B = (λ x → ∣ elim (λ _ → isset) (λ x → x) x ∣₀ ≡ x)}
      (λ x → hLevelSuc 2 ∥ A ∥₀ (setTruncIsSet {A = A}) ∣ elim (λ _ → isset) (λ x₁ → x₁) x ∣₀ x)
      (λ _ → refl)
      b

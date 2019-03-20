{-

This file contains:

- Properties of set truncations

-}
{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.SetTruncation.Properties where

open import Cubical.HITs.SetTruncation.Base

open import Cubical.Core.Prelude
open import Cubical.Core.Glue

open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels

private
  variable
    ℓ : Level
    A : Set ℓ

elimSquash₀ : {B : A → Set ℓ} →
              (Bset : (x : A ) → isSet (B x)) →
              {x y : A } {p q : x ≡ y} (sq : p ≡ q) → ∀ bx by bp bq →
              PathP (λ i → PathP (λ j → B (sq i j)) bx by) bp bq
elimSquash₀ {A = A} {B = B} Bset {p = p} =
  J (λ q sq → ∀ bx by bp bq →
    PathP (λ i → PathP (λ j → B (sq i j)) bx by) bp bq) (BsetOver' p)
    where
    BsetOver' : {x y : A } → (p : x ≡ y) → ∀ bx by bp bp' → bp ≡ bp'
    BsetOver' {x = x} = J (λ y (p : x ≡ y) → ∀ bx by →
      (bp bp' : PathP (λ i → B (p i)) bx by) → bp ≡ bp') (Bset x)

-- lemma 6.9.1 in HoTT book
elimSetTrunc : {B : ∥ A ∥₀ → Set ℓ} →
               (Bset : (x : ∥ A ∥₀) → isSet (B x)) →
               (g : (a : A) → B (∣ a ∣₀)) →
               (x : ∥ A ∥₀) → B x
elimSetTrunc Bset g ∣ a ∣₀ = g a
elimSetTrunc {A = A} {B = B} Bset g (squash₀ x y p q i j) =
  elimSquash₀ Bset (squash₀ x y p q) (elimSetTrunc Bset g x) (elimSetTrunc Bset g y)
    (cong (elimSetTrunc Bset g) p) (cong (elimSetTrunc Bset g) q) i j

setTruncUniversal : {B : Set ℓ} → (isSet B) → (∥ A ∥₀ → B) ≃ (A → B)
setTruncUniversal Bset = isoToEquiv (iso intro elim leftInv rightInv)
  where
  intro = (λ h a → h ∣ a ∣₀)
  elim = elimSetTrunc (λ x → Bset)

  leftInv : ∀ g → intro (elim g) ≡ g
  leftInv g = refl

  rightInv : ∀ h → elim (intro h) ≡ h
  rightInv h i x = elimSetTrunc (λ x → isProp→isSet (Bset (elim (intro h) x) (h x)))
                                (λ a → refl) x i

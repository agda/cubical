{-

This file contains:

- Definition of set truncation and its eliminator

It should *not* depend on the Agda standard library

-}

{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.SetTruncation where

open import Cubical.Core.Prelude
open import Cubical.Core.Glue

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.NTypes

-- set truncation as a higher inductive type:

data ∥_∥₀ {ℓ} (A : Set ℓ) : Set ℓ where
  ∣_∣₀ : A → ∥ A ∥₀
  squash₀ : ∀ (x y : ∥ A ∥₀) (p q : x ≡ y) → p ≡ q

private
  variable
    ℓ : Level
    A : Set ℓ

-- lemma 6.9.1 in HoTT book
elimSetTrunc : {B : ∥ A ∥₀ → Set ℓ} →
               ((x : ∥ A ∥₀) → isSet (B x)) →
               (g : (a : A) → B (∣ a ∣₀)) →
               (x : ∥ A ∥₀) → B x
elimSetTrunc Bset g ∣ a ∣₀ = g a 
elimSetTrunc {A = A} {B = B} Bset g (squash₀ x y p q i j) =
  BsetOver (squash₀ x y p q) (elimSetTrunc Bset g x) (elimSetTrunc Bset g y) (cong (elimSetTrunc Bset g) p) (cong (elimSetTrunc Bset g) q) i j
    where
    BsetOver' : {x y : ∥ A ∥₀} → (p : x ≡ y) → ∀ bx by bp bp' → bp ≡ bp'
    BsetOver' {x = x} = J (λ y (p : x ≡ y) → ∀ bx by → (bp bp' : PathP (λ i → B (p i)) bx by) → bp ≡ bp') (Bset x)

    BsetOver : {x y : ∥ A ∥₀} → {p q : x ≡ y} (sq : p ≡ q) → ∀ bx by bp bq → 
               PathP (λ i → PathP (λ j → B (sq i j)) bx by) bp bq
    BsetOver {x = x} {y = y} {p = p} = J (λ q (sq : p ≡ q) → ∀ bx by bp bq → PathP (λ i → PathP (λ j → B (sq i j)) bx by) bp bq) (BsetOver' p)


someEquiv : {B : Set ℓ} → (isSet B) → (∥ A ∥₀ → B) ≃ (A → B)
someEquiv {B = B} Bset = isoToEquiv intro elim (λ y → funExt (λ a → refl)) rightInv
  where
  intro = (λ h a → h ∣ a ∣₀) 
  elim = elimSetTrunc {B = λ x → B} (λ x → Bset)

  rightInv : ∀ h →  elim (intro h) ≡ h
  rightInv h = funExt (λ x → elimSetTrunc {B = λ x → elim (intro h) x ≡ h x} (λ x → isProp→isSet (Bset (elim (intro h) x) (h x))) (λ a → refl) x)

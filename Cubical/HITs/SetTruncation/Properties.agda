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
elimSetTrunc : {B : ∥ A ∥₀ → Type ℓ} →
               (Bset : (x : ∥ A ∥₀) → isSet (B x)) →
               (g : (a : A) → B (∣ a ∣₀)) →
               (x : ∥ A ∥₀) → B x
elimSetTrunc Bset g ∣ a ∣₀ = g a
elimSetTrunc {A = A} {B = B} Bset g (squash₀ x y p q i j) =
  isOfHLevel→isOfHLevelDep 2 Bset  (elimSetTrunc Bset g x) (elimSetTrunc Bset g y)
    (cong (elimSetTrunc Bset g) p) (cong (elimSetTrunc Bset g) q) (squash₀ x y p q) i j

setTruncUniversal : {B : Type ℓ} → (isSet B) → (∥ A ∥₀ → B) ≃ (A → B)
setTruncUniversal Bset = isoToEquiv (iso intro elim leftInv rightInv)
  where
  intro = (λ h a → h ∣ a ∣₀)
  elim = elimSetTrunc (λ x → Bset)

  leftInv : ∀ g → intro (elim g) ≡ g
  leftInv g = refl

  rightInv : ∀ h → elim (intro h) ≡ h
  rightInv h i x = elimSetTrunc (λ x → isProp→isSet (Bset (elim (intro h) x) (h x)))
                                (λ a → refl) x i

elimSetTrunc2 : {B : ∥ A ∥₀ → ∥ A ∥₀ → Type ℓ}
                (Bset : ((x y : ∥ A ∥₀) → isSet (B x y)))
                (g : (a b : A) → B ∣ a ∣₀ ∣ b ∣₀)
                (x y : ∥ A ∥₀) → B x y
elimSetTrunc2 Bset g = elimSetTrunc (λ _ → isOfHLevelPi 2 (λ _ → Bset _ _)) (λ a →
                       elimSetTrunc (λ _ → Bset _ _) (λ b → g a b))

elimSetTrunc3 : {B : (x y z : ∥ A ∥₀) → Type ℓ}
                (Bset : ((x y z : ∥ A ∥₀) → isSet (B x y z)))
                (g : (a b c : A) → B ∣ a ∣₀ ∣ b ∣₀ ∣ c ∣₀)
                (x y z : ∥ A ∥₀) → B x y z
elimSetTrunc3 Bset g = elimSetTrunc2 (λ _ _ → isOfHLevelPi 2 λ _ → Bset _ _ _) (λ a b →
                       elimSetTrunc (λ _ → Bset _ _ _) (λ c → g a b c))

setTruncIsSet : isSet ∥ A ∥₀
setTruncIsSet a b p q = squash₀ a b p q

setId : isSet A → ∥ A ∥₀ ≡ A
setId {A = A} isset = isoToPath (iso (elimSetTrunc {A = A}
                                                  (λ _ → isset)
                                                  (λ x → x))
                                     (λ x → ∣ x ∣₀)
                                     (λ b → refl)
                                     λ b → idLemma b)
  where
  idLemma : ∀ (b : ∥ A ∥₀) → ∣ elimSetTrunc (λ x → isset) (λ x → x) b ∣₀ ≡ b
  idLemma b = elimSetTrunc {B = (λ x → ∣ elimSetTrunc (λ _ → isset) (λ x → x) x ∣₀ ≡ x)}
                          (λ x → (isOfHLevelSuc 2 (setTruncIsSet {A = A}))
                                 ∣ elimSetTrunc (λ _ → isset) (λ x₁ → x₁) x ∣₀
                                 x)
                          (λ _ → refl)
                          b

{-

This file contains:
  - The reduced version gives the same type as James.

-}
{-# OPTIONS --safe --lossy-unification #-}
module Cubical.HITs.James.Inductive.ColimitEquivalence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Pointed

open import Cubical.HITs.James.Base
  renaming (James to JamesConstruction)
open import Cubical.HITs.James.Inductive.Reduced
  renaming (𝕁Red to 𝕁RedConstruction ; 𝕁Red∞ to 𝕁amesConstruction)
open import Cubical.HITs.James.Inductive.Coherence

private
  variable
    ℓ : Level

module _
  ((X , x₀) : Pointed ℓ) where

  private
    James = JamesConstruction (X , x₀)
    𝕁ames = 𝕁amesConstruction (X , x₀)
    𝕁Red  =  𝕁RedConstruction (X , x₀)

  -- Mimicking the constructors in each other

  unit' : (x : X)(xs : James) → Path James (x₀ ∷ x ∷ xs) (x ∷ x₀ ∷ xs)
  unit' x xs = sym (unit (x ∷ xs)) ∙∙ refl ∙∙ (λ i → x ∷ unit xs i)

  coh' : (xs : James) → refl ≡ unit' x₀ xs
  coh' xs i j =
    coh-helper {A = James} (unit xs) (unit (x₀ ∷ xs))
      (λ i → x₀ ∷ unit xs i) (λ i j → unit (unit xs j) i) i j

  _∷∞_ : X → 𝕁ames → 𝕁ames
  _∷∞_ x (inl xs) = inl (x ∷ xs)
  _∷∞_ x (push xs i) = (push (x ∷ xs) ∙ (λ i → inl (unit x xs i))) i

  push∞ : (xs : 𝕁ames) → xs ≡ x₀ ∷∞ xs
  push∞ (inl xs) = push xs
  push∞ (push xs i) j =
    push-helper {A = 𝕁ames} (push xs) (push (x₀ ∷ xs))
      (λ i → inl (unit x₀ xs i)) (λ i j → inl (coh xs i j)) j i

  infixr 5 _∷∞_

  -- One side map

  𝕁→James-inl : 𝕁Red → James
  𝕁→James-inl [] = []
  𝕁→James-inl (x ∷ xs) = x ∷ 𝕁→James-inl xs
  𝕁→James-inl (unit x xs i) = unit' x (𝕁→James-inl xs) i
  𝕁→James-inl (coh xs i j) = coh' (𝕁→James-inl xs) i j

  𝕁→James : 𝕁ames → James
  𝕁→James (inl xs) = 𝕁→James-inl xs
  𝕁→James (push xs i) = unit (𝕁→James-inl xs) i

  -- Commutativity with pseudo-constructors

  𝕁→James-∷ : (x : X)(xs : 𝕁ames) → 𝕁→James (x ∷∞ xs) ≡ x ∷ 𝕁→James xs
  𝕁→James-∷ x (inl xs) = refl
  𝕁→James-∷ x (push xs i) j = comp-cong-helper 𝕁→James (push (x ∷ xs)) _ (λ i → inl (unit x xs i)) refl j i

  𝕁→James-push : (xs : 𝕁ames)
    → PathP (λ i → 𝕁→James xs ≡ 𝕁→James-∷ x₀ xs i) (cong 𝕁→James (push∞ xs)) (unit (𝕁→James xs))
  𝕁→James-push (inl xs) = refl
  𝕁→James-push (push xs i) j k =
    hcomp (λ l → λ
      { (i = i0) → unit (𝕁→James-inl xs) k
      ; (i = i1) → unit (x₀ ∷ 𝕁→James-inl xs) k
      ; (j = i0) →
          push-helper-cong 𝕁→James (push xs) (push (x₀ ∷ xs))
            (λ i → inl (unit x₀ xs i)) (λ i j → inl (coh xs i j)) k i (~ l)
      ; (j = i1) → unit (unit (𝕁→James-inl xs) i) k
      ; (k = i0) → unit (𝕁→James-inl xs) i
      ; (k = i1) →
          comp-cong-helper-filler 𝕁→James (push (x₀ ∷ xs)) _
            (λ i → inl (unit x₀ xs i)) refl j i l })
    (push-coh-helper _ _ _ (λ i j → unit (unit (𝕁→James-inl xs) j) i) k i j)

  -- The other-side map

  private
    push-square : (x : X)(xs : 𝕁Red)
      → sym (push (x ∷ xs)) ∙∙ refl ∙∙ (λ i → x ∷∞ push xs i) ≡ (λ i → inl (unit x xs i))
    push-square x xs i j = push-square-helper (push (x ∷ xs)) (λ i → inl (unit x xs i)) i j

    coh-cube : (xs : 𝕁Red)
      → SquareP
          (λ i j → coh-helper _ _ _ (λ i j → push∞ (push xs j) i) i j ≡ inl (coh xs i j))
          (λ i j → inl (x₀ ∷ x₀ ∷ xs))
          (λ i j → push-square-helper (push (x₀ ∷ xs))
                    (λ i → inl (unit x₀ xs i)) j i)
          (λ i j → inl (x₀ ∷ x₀ ∷ xs))
          (λ i j → inl (x₀ ∷ x₀ ∷ xs))
    coh-cube xs =
      coh-cube-helper {A = 𝕁ames} (push xs) (push (x₀ ∷ xs))
        (λ i → inl (unit x₀ xs i)) (λ i j → inl (coh xs i j))

  J→𝕁ames : James → 𝕁ames
  J→𝕁ames [] = inl []
  J→𝕁ames (x ∷ xs) = x ∷∞ (J→𝕁ames xs)
  J→𝕁ames (unit xs i) = push∞ (J→𝕁ames xs) i

  -- The following is the most complicated part.
  -- It seems horrible but mainly it's due to correction of boudaries.

  𝕁→J→𝕁ames-inl : (xs : 𝕁Red) → J→𝕁ames (𝕁→James (inl xs)) ≡ inl xs
  𝕁→J→𝕁ames-inl [] = refl
  𝕁→J→𝕁ames-inl (x ∷ xs) t = x ∷∞ 𝕁→J→𝕁ames-inl xs t
  𝕁→J→𝕁ames-inl (unit x xs i) j =
    hcomp (λ k → λ
      { (i = i0) → square-helper (j ∨ ~ k) i0
      ; (i = i1) → square-helper (j ∨ ~ k) i1
      ; (j = i0) → square-helper (~ k) i
      ; (j = i1) → inl (unit x xs i) })
    (push-square x xs j i)
    where
      square-helper : (i j : I) → 𝕁ames
      square-helper i j =
        doubleCompPath-cong-filler J→𝕁ames
          (sym (unit (x ∷ 𝕁→James-inl xs))) refl (λ i → x ∷ unit (𝕁→James-inl xs) i)
          (λ i j → push∞ (x ∷∞ 𝕁→J→𝕁ames-inl xs i) (~ j))
          (λ i j → x ∷∞ 𝕁→J→𝕁ames-inl xs i)
          (λ i j → x ∷∞ push∞ (𝕁→J→𝕁ames-inl xs i) j) i j i1
  𝕁→J→𝕁ames-inl (coh xs i j) k =
    hcomp (λ l → λ
      { (i = i0) → cube-helper i0 j (k ∨ ~ l)
      ; (i = i1) → inl-filler j k l
      ; (j = i0) → cube-helper i i0 (k ∨ ~ l)
      ; (j = i1) → cube-helper i i1 (k ∨ ~ l)
      ; (k = i0) → cube-helper i j (~ l)
      ; (k = i1) → inl (coh xs i j) })
    (coh-cube xs i j k)
    where
      cube-helper : (i j k : I) → 𝕁ames
      cube-helper i j k =
        coh-helper-cong J→𝕁ames _ _ _
          (λ i j → unit (unit (𝕁→James-inl xs) j) i)
          (λ i j k → push∞ (push∞ (𝕁→J→𝕁ames-inl xs k) j) i) i j k

      inl-filler : (i j k : I) → 𝕁ames
      inl-filler i j k =
        hfill (λ k → λ
          { (i = i0) → square-helper (j ∨ ~ k) i0
          ; (i = i1) → square-helper (j ∨ ~ k) i1
          ; (j = i0) → square-helper (~ k) i
          ; (j = i1) → inl (unit x₀ xs i) })
        (inS (push-square x₀ xs j i)) k
        where
          square-helper : (i j : I) → 𝕁ames
          square-helper i j =
            doubleCompPath-cong-filler J→𝕁ames
              (sym (unit (x₀ ∷ 𝕁→James-inl xs))) refl (λ i → x₀ ∷ unit (𝕁→James-inl xs) i)
              (λ i j → push∞ (x₀ ∷∞ 𝕁→J→𝕁ames-inl xs i) (~ j))
              (λ i j → x₀ ∷∞ 𝕁→J→𝕁ames-inl xs i)
              (λ i j → x₀ ∷∞ push∞ (𝕁→J→𝕁ames-inl xs i) j) i j i1

  -- The main equivalence

  𝕁→J→𝕁ames : (xs : 𝕁ames) → J→𝕁ames (𝕁→James xs) ≡ xs
  𝕁→J→𝕁ames (inl xs) = 𝕁→J→𝕁ames-inl xs
  𝕁→J→𝕁ames (push xs i) j = push∞ (𝕁→J→𝕁ames-inl xs j) i

  J→𝕁→James : (xs : James) → 𝕁→James (J→𝕁ames xs) ≡ xs
  J→𝕁→James [] = refl
  J→𝕁→James (x ∷ xs) = 𝕁→James-∷ x (J→𝕁ames xs) ∙ (λ i → x ∷ J→𝕁→James xs i)
  J→𝕁→James (unit xs i) j =
    hcomp (λ k → λ
      { (i = i0) → J→𝕁→James xs (j ∧ k)
      ; (i = i1) → compPath-filler (𝕁→James-∷ x₀ (J→𝕁ames xs)) (λ i → x₀ ∷ J→𝕁→James xs i) k j
      ; (j = i0) → 𝕁→James (J→𝕁ames (unit xs i))
      ; (j = i1) → unit (J→𝕁→James xs k) i })
    (𝕁→James-push (J→𝕁ames xs) j i)

  James≃𝕁Red∞ : James ≃ 𝕁ames
  James≃𝕁Red∞ = isoToEquiv (iso J→𝕁ames 𝕁→James 𝕁→J→𝕁ames J→𝕁→James)

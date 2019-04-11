{-# OPTIONS --cubical --safe #-}
module Cubical.Relation.Nullary.DecidableEq where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude

open import Cubical.Data.Empty

open import Cubical.Relation.Nullary

-- Proof of Hedberg's theorem: a type with decidable equality is an h-set

Dec→Stable : ∀ {ℓ} (A : Type ℓ) → Dec A → Stable A
Dec→Stable A (yes x) = λ _ → x
Dec→Stable A (no x) = λ f → ⊥-elim (f x)

Stable≡→isSet : ∀ {ℓ} {A : Type ℓ} → (st : ∀ (a b : A) → Stable (a ≡ b)) → isSet A
Stable≡→isSet {A = A} st a b p q j i =
  let f : (x : A) → a ≡ x → a ≡ x
      f x p = st a x (λ h → h p)
      fIsConst : (x : A) → (p q : a ≡ x) → f x p ≡ f x q
      fIsConst = λ x p q i → st a x (isProp¬ _ (λ h → h p) (λ h → h q) i)
      rem : (p : a ≡ b) → PathP (λ i → a ≡ p i) (f a refl) (f b p)
      rem p j = f (p j) (λ i → p (i ∧ j))
  in hcomp (λ k → λ { (i = i0) → f a refl k
                    ; (i = i1) → fIsConst b p q j k
                    ; (j = i0) → rem p i k
                    ; (j = i1) → rem q i k }) a

-- Hedberg's theorem
Discrete→isSet : ∀ {ℓ} {A : Type ℓ} → Discrete A → isSet A
Discrete→isSet d = Stable≡→isSet (λ x y → Dec→Stable (x ≡ y) (d x y))

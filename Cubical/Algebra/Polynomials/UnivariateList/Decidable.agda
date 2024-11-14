{-# OPTIONS --safe #-}
module Cubical.Algebra.Polynomials.UnivariateList.Decidable where

{-
Polynomials over commutative rings with decidable equality
==========================================================
-}


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Relation.Nullary.Base using (decRec; ¬_)
open import Cubical.Relation.Nullary.DecidablePropositions

open import Cubical.Data.Sigma
open import Cubical.Data.Nat renaming (_+_ to _Nat+_; _·_ to _Nat·_) hiding (·-comm)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Bool hiding (_≤_)
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.Group
open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing

open import Cubical.Algebra.Polynomials.UnivariateList.Base

private variable
  ℓ : Level

{-
 if a sequence of decidable properties starting with a false one, becomes eventually true,
 there is a highest natural number for which it is false
-}
lemma : (s : ℕ → DecProp ℓ)
        → ¬ (s zero .fst .fst)
        → ∃[ k ∈ ℕ ] ((l : ℕ) → k ≤ l → (s l) .fst .fst)
        → Σ[ n ∈ ℕ ] ((¬ ((s n) .fst .fst)) × ((l : ℕ) → suc n ≤ l → (s l) .fst .fst))
lemma s s-zero eventuallyHolds =
  PT.rec isPropLatestCounterexamples
         (λ {(k , p) → byInduction k p})
         eventuallyHolds
  where isPropLatestCounterexamples : isProp (Σ[ n ∈ ℕ ] ((¬ ((s n) .fst .fst)) × ((l : ℕ) → suc n ≤ l → (s l) .fst .fst)))
        isPropLatestCounterexamples (n , p) (n' , p') =
          Σ≡Prop (λ x → isProp× (isPropΠ (λ _ → isProp⊥)) (isPropΠ λ _ → isPropΠ λ _ → s _ .fst .snd))
                 (≤CaseInduction {P = _≡_}
                   (λ n≤n' → Sum.rec (λ suc-n≤n' → ⊥.rec ((p' .fst) (p .snd n' suc-n≤n') )) (λ n≡n' → n≡n') (≤-split n≤n'))
                   (λ n'≤n → Sum.rec (λ suc-n'≤n → ⊥.rec ((p .fst) (p' .snd n suc-n'≤n))) sym (≤-split n'≤n)))

        byInduction : (k' : ℕ) → ((l : ℕ) → k' ≤ l → (s l) .fst .fst)
                      → Σ[ n ∈ ℕ ] ((¬ ((s n) .fst .fst)) × ((l : ℕ) → suc n ≤ l → (s l) .fst .fst))
        byInduction zero    eventuallyHolds = zero , s-zero , λ l → λ 1≤l → eventuallyHolds l (≤-trans zero-≤ 1≤l)
        byInduction (suc k) eventuallyHolds =
          decRec (λ p →
                    byInduction k
                                (λ l k≤l → Sum.rec (λ k<l → eventuallyHolds l k<l)
                                                   (λ k≡l → subst (λ l → s l .fst .fst) k≡l p)
                                                   (≤-split k≤l)))
                 (λ ¬p → k , ¬p , (λ l k+1≤l → eventuallyHolds l k+1≤l))
                 (s k .snd)

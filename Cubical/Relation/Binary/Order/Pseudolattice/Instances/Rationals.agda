module Cubical.Relation.Binary.Order.Pseudolattice.Instances.Rationals where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Rationals
open import Cubical.Data.Rationals.Order renaming (_≤_ to _≤ℚ_)

open import Cubical.Relation.Binary.Order.Poset.Instances.Rationals
open import Cubical.Relation.Binary.Order.Pseudolattice

ℚ≤Pseudolattice : Pseudolattice ℓ-zero ℓ-zero
ℚ≤Pseudolattice = makePseudolatticeFromPoset ℚ≤Poset min max
  (λ {a b}   → min≤ a b)
  (λ {a b}   → recompute≤ (subst (_≤ℚ b) (minComm b a) (min≤ b a)))
  (λ {a b x} → ((recompute≤ ∘ subst (_≤ℚ min a b) (minIdem x)) ∘_) ∘ ≤MonotoneMin x a x b)
  (λ {x} {y} → ≤max x y)
  (λ {a b}   → recompute≤ (subst (b ≤ℚ_) (maxComm b a) (≤max b a)))
  (λ {a b x} → ((recompute≤ ∘ subst (max a b ≤ℚ_) (maxIdem x)) ∘_) ∘ ≤MonotoneMax a x b x)

module Cubical.Relation.Binary.Order.Pseudolattice.Instances.Rationals.Fast where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals.Fast
open import Cubical.Data.Rationals.Fast.Order renaming (_≤_ to _≤ℚ_)

open import Cubical.Relation.Binary.Order.Poset.Instances.Rationals.Fast
open import Cubical.Relation.Binary.Order.Pseudolattice

ℚ≤Pseudolattice : Pseudolattice ℓ-zero ℓ-zero
ℚ≤Pseudolattice = makePseudolatticeFromPoset ℚ≤Poset min max
  (λ {a b} → min≤ a b)
  (λ {a b} → subst (_≤ℚ b) (minComm b a) (min≤ b a))
  (λ {a b x} x≤a x≤b → subst (_≤ℚ min a b) (minIdem x) (≤MonotoneMin x a x b x≤a x≤b))
  (λ {x} {y} → ≤max x y)
  (λ {a b} → subst (b ≤ℚ_) (maxComm b a) (≤max b a))
  (λ {a b x} a≤x b≤x → subst (max a b ≤ℚ_) (maxIdem x) (≤MonotoneMax a x b x a≤x b≤x))

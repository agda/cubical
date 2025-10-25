module Cubical.Relation.Binary.Order.Pseudolattice.Instances.Int where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Int
open import Cubical.Data.Int.Order renaming (_≤_ to _≤ℤ_)

open import Cubical.Relation.Binary.Order.Poset.Instances.Int
open import Cubical.Relation.Binary.Order.Pseudolattice

ℤ≤Pseudolattice : Pseudolattice ℓ-zero ℓ-zero
ℤ≤Pseudolattice = makePseudolatticeFromPoset ℤ≤Poset min max
  min≤
  (λ {a b} → subst (_≤ℤ b) (minComm b a) min≤)
  (λ {a b} x≤a x≤b → subst (_≤ℤ min a b) (minIdem _) (≤MonotoneMin x≤a x≤b))
  ≤max
  (λ {a b} → subst (b ≤ℤ_) (maxComm b a) ≤max)
  (λ {a b} a≤x b≤x → subst (max a b ≤ℤ_) (maxIdem _) (≤MonotoneMax a≤x b≤x))

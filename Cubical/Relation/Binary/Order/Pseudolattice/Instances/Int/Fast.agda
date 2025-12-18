module Cubical.Relation.Binary.Order.Pseudolattice.Instances.Int.Fast where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Int.Fast
open import Cubical.Data.Int.Fast.Order renaming (_≤_ to _≤ℤ_)

open import Cubical.Relation.Binary.Order.Poset.Instances.Int.Fast
open import Cubical.Relation.Binary.Order.Pseudolattice

ℤ≤Pseudolattice : Pseudolattice ℓ-zero ℓ-zero
ℤ≤Pseudolattice = makePseudolatticeFromPoset ℤ≤Poset min max
  min≤
  (λ {a b} → subst (_≤ℤ b) (minComm b a) min≤)
  (λ {a b x} x≤a x≤b → subst (_≤ℤ min a b) (minIdem x) (≤MonotoneMin {x} x≤a x≤b))
  ≤max
  (λ {a b} → subst (b ≤ℤ_) (maxComm b a) ≤max)
  (λ {a b x} a≤x b≤x → subst (max a b ≤ℤ_) (maxIdem x) (≤MonotoneMax {a} {x} {b} a≤x b≤x))

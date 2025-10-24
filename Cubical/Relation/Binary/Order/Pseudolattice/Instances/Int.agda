module Cubical.Relation.Binary.Order.Pseudolattice.Instances.Int where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Int
open import Cubical.Data.Int.Order renaming (_≤_ to _≤ℤ_)

open import Cubical.Relation.Binary.Order.Poset.Instances.Int
open import Cubical.Relation.Binary.Order.Pseudolattice

open PseudolatticeStr

ℤ≤Pseudolattice : Pseudolattice ℓ-zero ℓ-zero
ℤ≤Pseudolattice = makePseudolatticeFromPoset ℤ≤Poset min max
  (λ       x≤min → isTrans≤ x≤min min≤)
  (λ {a b} x≤min → isTrans≤ x≤min (subst (_≤ℤ b) (minComm b a) min≤))
  (λ {a b} x≤a x≤b → subst (_≤ℤ min a b) (minIdem _) (≤MonotoneMin x≤a x≤b))
  (λ       max≤x → isTrans≤ ≤max max≤x)
  (λ {a b} max≤x → isTrans≤ (subst (b ≤ℤ_) (maxComm b a) ≤max) max≤x)
  (λ {a b} a≤x b≤x → subst (max a b ≤ℤ_) (maxIdem _) (≤MonotoneMax a≤x b≤x))

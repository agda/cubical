module Cubical.Relation.Binary.Order.Pseudolattice.Instances.Nat where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Bool.Base

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order renaming (_≤_ to _≤ℕ_)

open import Cubical.Relation.Binary.Order.Poset.Instances.Nat
open import Cubical.Relation.Binary.Order.Pseudolattice

open PseudolatticeStr

private
  minGLB : ∀ {m n x} → x ≤ℕ m → x ≤ℕ n → x ≤ℕ min m n
  minGLB {zero}  {n}     x≤0 _     = x≤0
  minGLB {suc m} {zero}  _   x≤0   = x≤0
  minGLB {suc m} {suc n} x≤sm x≤sn with m <ᵇ n
  ... | false = x≤sn
  ... | true  = x≤sm

  maxLUB : ∀ {m n x} → m ≤ℕ x → n ≤ℕ x → max m n ≤ℕ x
  maxLUB {zero}  {n}     _    n≤x  = n≤x
  maxLUB {suc m} {zero}  sm≤x _    = sm≤x
  maxLUB {suc m} {suc n} sm≤x sn≤x with m <ᵇ n
  ... | false = sm≤x
  ... | true  = sn≤x

ℕ≤Pseudolattice : Pseudolattice ℓ-zero ℓ-zero
ℕ≤Pseudolattice = makePseudolatticeFromPoset ℕ≤Poset min max
  (λ       x≤min → ≤-trans x≤min min-≤-left)
  (λ {a b} x≤min → ≤-trans x≤min (min-≤-right {a} {b}))
  minGLB
  (λ       max≤x → ≤-trans left-≤-max max≤x)
  (λ {a b} max≤x → ≤-trans (right-≤-max {b} {a}) max≤x)
  maxLUB

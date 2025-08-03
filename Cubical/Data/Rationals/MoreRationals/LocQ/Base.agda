module Cubical.Data.Rationals.MoreRationals.LocQ.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset
open import Cubical.Relation.Nullary
open import Cubical.Data.Empty
open import Cubical.Data.Int as ℤ
open import Cubical.Data.Int.Order
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.HITs.SetQuotients
open import Cubical.Algebra.CommRing.Instances.Int
open import Cubical.Algebra.CommRing.Localisation

isPositive : ℙ ℤ
isPositive n .fst = n > 0
isPositive n .snd = isProp< {m = 0}

isPositiveMultclosed : isMultClosedSubset ℤCommRing isPositive
isPositiveMultclosed = multclosedsubset (0 , refl) λ {s} {t} s>0 t>0 →
  0<o→<-·o {o = t} {m = 0} {n = s} t>0 s>0

module Locℚ = Loc ℤCommRing isPositive isPositiveMultclosed

open Locℚ using (_≈_) renaming (
    S to Positive; S⁻¹R to ℚ; S⁻¹RAsCommRing to ℚCommRing;
    locRefl to ≈refl; locSym to ≈sym; locTrans to ≈trans; locIsEquivRel to ≈isEquivRel;
    _+ₗ_ to _+_; +ₗ-assoc to +-assoc; +ₗ-rid to +-rid; +ₗ-comm to +-comm; -ₗ_ to -_; +ₗ-rinv to +-rinv;
    _·ₗ_ to _·_; ·ₗ-assoc to ·-assoc; ·ₗ-rid to ·-rid; ·ₗ-comm to ·-comm
  ) public

module ℚUniversalProp = S⁻¹RUniversalProp ℤCommRing isPositive isPositiveMultclosed

open ℚUniversalProp using (_/1; /1AsCommRingHom) renaming (
    S⁻¹Rˣ to ℚˣ; S/1⊆S⁻¹Rˣ to ℤ⁺⊆ℚˣ; S⁻¹RHasUniversalProp to ℚHasUniversalProp
  )

--- Natural number and negative integer literals for ℚ

open import Cubical.Data.Nat.Literals public

instance
  fromNatPositive : HasFromNat Positive
  fromNatPositive .HasFromNat.Constraint zero = ⊥
  fromNatPositive .HasFromNat.Constraint (suc n) = Unit
  fromNatPositive .HasFromNat.fromNat (suc n) = pos (suc n) , n , ℤ.+Comm 1 (pos n)

  fromNatℚ : HasFromNat ℚ
  fromNatℚ = record { Constraint = λ _ → Unit ; fromNat = λ n → pos n /1 }

  fromNegℚ : HasFromNeg ℚ
  fromNegℚ = record { Constraint = λ _ → Unit ; fromNeg = λ n → neg n /1 }

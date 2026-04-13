{-

ℚ is a Field

-}
module Cubical.Algebra.Field.Instances.Rationals where

open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Rationals
open import Cubical.Algebra.Field

open import Cubical.Data.Empty as Empty
open import Cubical.Data.Int as ℤ
open import Cubical.Data.Nat as ℕ using (ℕ ; zero ; suc)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Rationals as ℚ
open import Cubical.Data.Rationals.Order.Properties
open import Cubical.Data.Sigma

open import Cubical.HITs.SetQuotients as SetQuotients

open import Cubical.Relation.Nullary

open CommRingStr (ℚCommRing .snd)
open Units        ℚCommRing

0≢1-ℚ : ¬ Path ℚ 0 1
0≢1-ℚ p = 0≢1-ℤ (effective (λ _ _ → isSetℤ _ _) isEquivRel∼ _ _ p)

ℚField : Field ℓ-zero
ℚField = makeFieldFromCommRing ℚCommRing hasInverseℚ 0≢1-ℚ

_[_]⁻¹ : (x : ℚ) → ¬ x ≡ 0 → ℚ
_[_]⁻¹ = FieldStr._[_]⁻¹ $ snd ℚField

_/_[_] : ℚ → (y : ℚ) → ¬ y ≡ 0 → ℚ
x / y [ p ] = x ℚ.· (y [ p ]⁻¹)

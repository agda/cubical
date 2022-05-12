{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.ZCohomology.CohomologyRings.S0 where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Bool
open import Cubical.Data.Nat renaming (_+_ to _+n_ ; _·_ to _·n_ ; snotz to nsnotz)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.AbGroup.Instances.DirectSum
open import Cubical.Algebra.DirectSum.Base
open import Cubical.Algebra.Ring
open import Cubical.Algebra.Ring.DirectProd
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Int renaming (ℤCommRing to ℤCR)
open import Cubical.Algebra.CommRing.FGIdeal
open import Cubical.Algebra.CommRing.QuotientRing
open import Cubical.Algebra.Polynomials.Multivariate.Base renaming (base to baseP)
open import Cubical.Algebra.CommRing.Instances.MultivariatePoly
open import Cubical.Algebra.CommRing.Instances.MultivariatePoly-Quotient
open import Cubical.Algebra.CommRing.Instances.MultivariatePoly-notationZ

open import Cubical.HITs.Sn

open import Cubical.ZCohomology.RingStructure.CohomologyRing
open import Cubical.ZCohomology.CohomologyRings.Coproduct
open import Cubical.ZCohomology.CohomologyRings.Unit


-----------------------------------------------------------------------------
-- Warning
-- H*(S0) is not Z[X]/X²
-- It is Z[X]/X × Z[X]/X or Z[X] /(X² - X)
-- Beware that H*(X ⊔ Y) ≅ H*(X) × H*(Y)
-- Which would apply for H*(Unit ⊔ Unit)


-----------------------------------------------------------------------------
-- Computation of the cohomology ring

open RingEquivs

Cohomology-Ring-S⁰P : RingEquiv (H*R (S₊ 0)) (DirectProd-Ring (CommRing→Ring ℤ[X]/X) (CommRing→Ring ℤ[X]/X))
Cohomology-Ring-S⁰P =  compRingEquiv (CohomologyRing-Equiv (invIso Iso-⊤⊎⊤-Bool))
                     (compRingEquiv (CohomologyRing-Coproduct Unit Unit)
                                    (Coproduct-Equiv.Coproduct-Equiv-12 CohomologyRing-UnitP CohomologyRing-UnitP))

Cohomology-Ring-S⁰ℤ : RingEquiv (H*R (S₊ 0)) (DirectProd-Ring (CommRing→Ring ℤCR) (CommRing→Ring ℤCR))
Cohomology-Ring-S⁰ℤ =  compRingEquiv (CohomologyRing-Equiv (invIso Iso-⊤⊎⊤-Bool))
                     (compRingEquiv (CohomologyRing-Coproduct Unit Unit)
                                    (Coproduct-Equiv.Coproduct-Equiv-12 CohomologyRing-Unitℤ CohomologyRing-Unitℤ))

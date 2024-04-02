{-

Please do not move this file. Changes should only be made if necessary.

This file contains pointers to the code examples and main results from
the paper:

Computing Cohomology Rings in Cubical Agda

-}

-- The "--safe" flag ensures that there are no postulates or unfinished goals
{-# OPTIONS --safe #-}
module Cubical.Papers.CohomologyRings where

-- 1: Introduction

import Cubical.ZCohomology.Groups.S2wedgeS1wedgeS1                as HⁿS²∨S¹∨S¹

-- 2: Background

open import Cubical.Foundations.Prelude                           as Prelude
open import Cubical.Data.Sigma                                    as Sigma
import Cubical.HITs.PropositionalTruncation                       as PT
import Cubical.HITs.SetTruncation                                 as ST
import Cubical.HITs.Truncation                                    as Trunc
import Cubical.Foundations.Pointed                                as Pointed
import Cubical.Algebra.Group                                      as Group
import Cubical.Algebra.AbGroup                                    as AbGroup
import Cubical.Cohomology.EilenbergMacLane.Base                   as G-Kⁱ
import Cubical.Homotopy.EilenbergMacLane.GroupStructure           as G-Kⁱ-Group
import Cubical.Homotopy.EilenbergMacLane.CupProduct               as G-Kⁱ-Cup
import Cubical.Cohomology.EilenbergMacLane.CupProduct             as G-H*

-- 3: Formalizing graded rings

import Cubical.Algebra.DirectSum.DirectSumFun.Base                as ⊕Fun
open import Cubical.Algebra.DirectSum.DirectSumFun.Properties     as ⊕FunProp
import Cubical.Algebra.DirectSum.DirectSumHIT.Base                as ⊕HIT
open import Cubical.Algebra.DirectSum.DirectSumHIT.Properties     as ⊕HITProp
import Cubical.Algebra.GradedRing.DirectSumFun                    as GradedRingFun
open import Cubical.Algebra.GradedRing.DirectSumHIT               as GradedRingHIT
open GradedRing-⊕HIT-index
import Cubical.Algebra.Ring                                       as Ring

-- 4: Polynomial rings

import Cubical.Algebra.Polynomials.UnivariateList.Base                   as ListPoly
import Cubical.Algebra.CommRing.Instances.Polynomials.UnivariatePolyFun  as UniPolyFun
import Cubical.Algebra.CommRing.Instances.Polynomials.UnivariatePolyHIT  as UniPolyHIT
import Cubical.Algebra.CommRing.Instances.Polynomials.MultivariatePoly   as MultiPolyHIT

-- 5: Cohomology rings

import Cubical.ZCohomology.RingStructure.CohomologyRing           as ℤCohomologyRing
import Cubical.HITs.S1                                            as S1
import Cubical.ZCohomology.CohomologyRings.S1                     as H*S¹
import Cubical.HITs.Susp                                          as Suspension
import Cubical.HITs.Sn                                            as Sn
import Cubical.ZCohomology.Groups.Sn                              as HⁿSᵐ
import Cubical.ZCohomology.CohomologyRings.Sn                     as H*Sᵐ
open import Cubical.Homotopy.Hopf                                 as HopfFibration
import Cubical.ZCohomology.Groups.CP2                             as HⁿℂP²
import Cubical.ZCohomology.CohomologyRings.CP2                    as H*ℂP²
import Cubical.HITs.Wedge                                         as ⋁
import Cubical.ZCohomology.Groups.S2wedgeS4                       as HⁿS²∨S⁴
import Cubical.ZCohomology.CohomologyRings.S2wedgeS4              as H*S²∨S⁴
import Cubical.Cohomology.EilenbergMacLane.RingStructure          as GCohomologyRing
import Cubical.HITs.KleinBottle                                   as 𝕂²
import Cubical.HITs.RPn.Base                                      as ℝP²
import Cubical.ZCohomology.Groups.KleinBottle                     as Hⁿ𝕂²
import Cubical.ZCohomology.CohomologyRings.KleinBottle            as H*𝕂²
import Cubical.ZCohomology.Groups.RP2wedgeS1                      as HⁿℝP²∨S¹
import Cubical.ZCohomology.CohomologyRings.RP2wedgeS1             as H*ℝP²∨S¹
import Cubical.Cohomology.EilenbergMacLane.Groups.KleinBottle     as ℤ/2-Hⁿ𝕂²
open import Cubical.Cohomology.EilenbergMacLane.Rings.KleinBottle as ℤ/2-H*𝕂²
import Cubical.Cohomology.EilenbergMacLane.Groups.RP2wedgeS1      as ℤ/2-HⁿℝP²∨S¹
import Cubical.Cohomology.EilenbergMacLane.Rings.RP2wedgeS1       as ℤ/2-H*ℝP²∨S¹
  renaming (RP²∨S¹-CohomologyRing to H*RP²∨S¹≅ℤ/2[X,Y]/<Y³,XY,X²>)


----- 1. INNTRODUCTION -----
{- This part only contains the spaces. The rest of the
   mathematics will be developed in the following section. -}

open S1 using (S¹)

-- Torus
𝕋² : Type ℓ-zero
𝕋² = S¹ × S¹

-- "Mickey mouse space”
open HⁿS²∨S¹∨S¹ using (S²⋁S¹⋁S¹)


----- 2. BACKGROUND -----

-- 2.1 Homotopy Type Theory in Cubical Agda

-- Path type in Cubical Agda
open Prelude using (PathP ; _≡_ ; funExt)
-- Interval operations
open Prelude using (_∧_ ; _∨_ ; ~_ )
-- Function extensionality
open Prelude using (funExt)
-- Equality of Σ-types
open Sigma using (ΣPathP)

-- Definition of S¹
open S1 using (S¹ ; base ; loop)
-- Inversion map for S¹
invS¹ : S¹ → S¹
invS¹ base = base
invS¹ (loop i) = loop (~ i)

-- Propositional truncation. In the agda/cubical library the
-- truncations is shifted by +2 and start at 0 instead of -2, hence
-- propositional truncation is ∥_∥₁.
open PT using (∥_∥₁)

-- ∃ notation in Cubical Agda
open Sigma using (∃-syntax)

-- Set truncation
open ST using (∥_∥₂)

-- General truncation, the index n is the second parameter here
open Trunc using (∥_∥_)

-- Pointed types
open Pointed using (Pointed)


-- 2.2 The structure identity principle

-- IsGroup is the group Ax, GroupStr is the raw structure + IsGroup
open Group using (IsGroup ; GroupStr )

-- The cubical SIP
import Cubical.Foundations.SIP

-- AbGroup induced by a raw group preserving equivalence and the path
-- to the other group
open AbGroup using (InducedAbGroup ; InducedAbGroupPath)


-- 2.3 Cohomology theory in Cubical Agda

-- G cohomology groups
open G-Kⁱ using (coHom ; coHomGr)
-- Eilenberg-MacLane space operations
open G-Kⁱ-Group using (_+ₖ_ ; -ₖ_)
open G-Kⁱ-Cup using (_⌣ₖ_)
-- Cohomology operations
open G-Kⁱ using (0ₕ)
open G-H* using (1ₕ ; ⌣-0ₕ ; 0ₕ-⌣ ; ⌣-1ₕ ; 1ₕ-⌣)


----- 3. FORMALIZING GRADED RINGS -----

-- 3.1 Direct sums

-- Fun direct Sum
open ⊕Fun using (⊕Fun)
open DSF-properties using (_+⊕Fun_ ; +⊕FunComm)

-- HIT direct sum
open ⊕HIT using (⊕HIT)
open AbGroupProperties using (inv)


-- 3.2 Graded rings

-- Product on the fun direct sum
open GradedRingFun using (_prodFun_ ; _prodF_)

-- Product on the HIT direct sum and properties
open GradedRing-⊕HIT-⋆ using (_prod_ ; prodAssoc ; ⊕HITgradedRing-Ring )
open GradedRing-⊕HIT-⋆
open ExtensionCommRing using (⊕HITgradedRing-CommRing)


-- 3.2.1 Transporting the ring structure using the SIP

-- Ring induced by a raw ring preserving equivalence
open Ring using (InducedRing ; InducedRingPath)

-- The induced CommRing structure on ⊕Fun
open GradedRingFun using (⊕HIT→⊕Fun-pres-prodF ; ⊕FunGradedRing-CommRing)



----- 4. POLYNOMIALS -----

-- 4.1 Polynomials as graded rings

-- Univariate polynomials as graded rings
open UniPolyFun using (UnivariatePolyFun-CommRing)
open UniPolyHIT using (UnivariatePolyHIT-CommRing)


-- 4.2 List based polynomials and decidable equality

open ListPoly using (Poly)


-- 4.3 Multivariate polynomials

open MultiPolyHIT using (PolyCommRing)

-- The isomorphism R[X₁,⋯,Xₙ]/(X₁,⋯,Xₙ) ≃ R
import Cubical.Algebra.Polynomials.Multivariate.EquivCarac.An[X]X-A
  using (Equiv-QuotientX-A)

-- CommRingEquiv (A[X1,···,Xn]/<X1,···,Xn> Ar n) Ar

----- 5. COHOMOLOGY RINGS -----

-- ℤ Cohomology rings
open ℤCohomologyRing using (H*R ; H*)


-- 5.1 Spheres

-- Proposition 5.1, Cohomology groups and ring of S¹
open S1   using (S¹)
open HⁿSᵐ using (Hⁿ-Sⁿ≅ℤ ; Hⁿ-Sᵐ≅0) -- includes the ones of S1 as special cases
open H*S¹ using (CohomologyRing-S¹)

-- Proposition 5.2, Cohomology groups and ring of Sⁿ
open Suspension using (Susp)
open Sn using (S₊)
open HⁿSᵐ using (Hⁿ-Sⁿ≅ℤ ; Hⁿ-Sᵐ≅0)
open H*Sᵐ using (CohomologyRing-Sⁿ)


-- 5.2 The complex projective plane

-- Definition of ℂP²

{- Note that S³ is defined as the total space of the Hopf fibration
   here. This is provably equivalent to S^3 and has been used by other
   users to simplify some proofs.  -}
open S¹Hopf using (TotalHopf)
open HⁿℂP² using (CP²)

-- Proposition 5.3, Cohomology groups and ring of ℂP²
open HⁿℂP² using (H⁰CP²≅ℤ ; H²CP²≅ℤ ; H⁴CP²≅ℤ ; Hⁿ-CP²≅0)
  -- the cup product
open HⁿℂP² using (H⁴CP²≅ℤ-pos-resp⌣)
open H*ℂP² using (CohomologyRing-CP²)

-- Definition of S² ∨ S⁴
open ⋁ using (_⋁_)
open HⁿS²∨S⁴ using (S²⋁S⁴)

-- Proposition 5.4, Cohomology groups and ring of S² ⋁ S⁴
open HⁿS²∨S⁴ using (H⁰-S²⋁S⁴≅ℤ ; H²-S²⋁S⁴≅ℤ ; H⁴-S²⋁S⁴≅ℤ ; Hⁿ-S²⋁S⁴≅0-bis)
open H*S²∨S⁴ using (CohomologyRing-S²⋁S⁴)


-- 5.3 The Klein bottle and the real projective plane with an adjoined circle

-- Definition of Klein bottle, ℝP², and ℝP² ⋁ S¹
open 𝕂² using (KleinBottle)
open ℝP² using (RP²)
open HⁿℝP²∨S¹ using (RP²⋁S¹)

-- ℤ Cohomology groups of the Klein Bottle and ℝP² ⋁ S¹
open Hⁿ𝕂² using (H⁰-𝕂²≅ℤ ; H¹-𝕂²≅ℤ ; H²-𝕂²≅Bool ; Hⁿ⁺³-𝕂²≅0)
open HⁿℝP²∨S¹ using (H⁰-RP²⋁S¹≅ℤ ; H¹-RP²⋁S¹≅ℤ ; H²-RP²⋁S¹≅Bool ; Hⁿ-RP²⋁S¹≅0)

-- Proposition 5.6, ℤ cohomology ring of the Klein Bottle and ℝP² ⋁ S¹
open H*𝕂² using (CohomologyRing-𝕂²)
open H*ℝP²∨S¹ using (CohomologyRing-RP²⋁S¹)

-- ℤ/2ℤ Cohomology groups of the Klein Bottle and ℝP² ⋁ S¹
open ℤ/2-Hⁿ𝕂² using (H⁰[K²,ℤ/2]≅ℤ/2 ; H¹[K²,ℤ/2]≅ℤ/2×ℤ/2 ; H²[K²,ℤ/2]≅ℤ/2 ; H³⁺ⁿ[K²,G]≅0)
open ℤ/2-HⁿℝP²∨S¹ using (H⁰[RP²∨S¹,ℤ/2]≅ℤ/2 ; H¹[RP²∨S¹,ℤ/2]≅ℤ/2×ℤ/2 ; H²[RP²∨S¹,ℤ/2]≅ℤ/2 ; H³⁺ⁿ[RP²∨S¹,ℤ/2]≅Unit)

-- Proposition 5.7, ℤ/2ℤ cohomology ring of the Klein Bottle
open ℤ/2-H*𝕂² using (H*KleinBottle≅ℤ/2[X,Y]/<X³,Y²,XY+X²>)

-- Proposition 5.8, ℤ/2ℤ cohomology ring of ℝP² ⋁ S¹
open ℤ/2-H*ℝP²∨S¹ using (H*RP²∨S¹≅ℤ/2[X,Y]/<Y³,XY,X²>)

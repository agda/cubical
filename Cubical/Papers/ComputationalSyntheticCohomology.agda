{-

Please do not move this file. Changes should only be made if necessary.

This file contains pointers to the code examples and main results from
the paper:

Computational Synthetic Cohomology Theory in Homotopy Type Theory

-}

-- The "--safe" flag ensures that there are no postulates or unfinished goals
{-# OPTIONS --safe #-}
module Cubical.Papers.ComputationalSyntheticCohomology where

open import Cubical.Data.Nat
open import Cubical.Algebra.AbGroup
open import Cubical.Foundations.GroupoidLaws

-- 1: Introduction
-- 2: Background

open import Cubical.Foundations.Prelude                           as Prelude
import Cubical.Homotopy.HSpace                                    as hSpace
import Cubical.Foundations.Pointed.Homogeneous                    as Homogeneous
import Cubical.HITs.Susp                                          as Suspensions
import Cubical.HITs.Pushout                                       as Pushouts
import Cubical.Foundations.Path                                   as Paths

-- 3:  Eilenberg-MacLane spaces
import Cubical.Homotopy.EilenbergMacLane.Base                     as EMSpace
import Cubical.Homotopy.EilenbergMacLane.Properties               as EMProps
import Cubical.Homotopy.EilenbergMacLane.WedgeConnectivity        as WC
import Cubical.Homotopy.EilenbergMacLane.GroupStructure           as EMGr
import Cubical.Algebra.AbGroup.TensorProduct                      as Tensor
import Cubical.Homotopy.EilenbergMacLane.CupProductTensor         as Cup⊗
import Cubical.Homotopy.EilenbergMacLane.CupProduct               as Cupₖ
import Cubical.Homotopy.EilenbergMacLane.GradedCommTensor         as CupComm

-- 4: Cohomology
import Cubical.Cohomology.EilenbergMacLane.Base                   as Cohom
import Cubical.Cohomology.EilenbergMacLane.CupProduct             as CohomCup
import Cubical.Axiom.Choice                                       as Choice
import Cubical.HITs.Wedge                                         as ⋁
import Cubical.Homotopy.EilenbergSteenrod                         as Axioms
import Cubical.Cohomology.EilenbergMacLane.EilenbergSteenrod      as SatAxioms
import Cubical.Cohomology.EilenbergMacLane.MayerVietoris          as MV
import Cubical.Cohomology.EilenbergMacLane.Gysin                  as Gysin

-- 5: Computations of cohomology groups and rings
import Cubical.Cohomology.EilenbergMacLane.Groups.Unit            as HⁿUnit
import Cubical.Cohomology.EilenbergMacLane.Groups.Connected       as CohomConnected
import Cubical.Cohomology.EilenbergMacLane.Groups.Sn              as CohomSn
import Cubical.Cohomology.EilenbergMacLane.Rings.Sn               as CohomRingSn
import Cubical.Cohomology.EilenbergMacLane.Groups.Torus           as CohomT²
import Cubical.HITs.Torus                                         as T²
import Cubical.HITs.RPn.Base                                      as RP²
import Cubical.HITs.KleinBottle                                   as K²
import Cubical.Cohomology.EilenbergMacLane.Groups.RP2             as CohomRP²
import Cubical.ZCohomology.CohomologyRings.RP2                    as ZCohomRingRP²
import Cubical.Cohomology.EilenbergMacLane.Groups.KleinBottle     as CohomK²
import Cubical.ZCohomology.CohomologyRings.KleinBottle            as ZCohomRingK²
import Cubical.Cohomology.EilenbergMacLane.Rings.RP2              as RP²Ring
import Cubical.Cohomology.EilenbergMacLane.Rings.KleinBottle      as K²Ring
import Cubical.Cohomology.EilenbergMacLane.Rings.RPinf            as RP∞Ring

----- 1. INNTRODUCTION -----

----- 2. Background on HoTT/UF and notations -----

-- 2.1 Homotopy Type Theory in Cubical Agda

-- Definition 1. Binary ap
open Prelude renaming (cong₂ to ap²)

-- Definition 2. H-spaces
open hSpace using (HSpace)

-- Definition 3. Homogeneous types
open Homogeneous using (isHomogeneous)

-- Definition 4. Suspension
open Suspensions using (Susp)

-- Definition 5. Pushouts
open Pushouts using (Pushout)

-- Lemma 6. Flip
open Paths using (sym≡flipSquare)

----- 3. Eilenberg-MacLane spaces -----
-- Definition 7.
-- Included for readability: not used explicitly in formalisation.

-- Definition 8. (raw Eilenbreg-MacLane spaces) EM-raw
open EMSpace using (EM-raw)

-- Definition 9. (Eilenbreg-MacLane spaces) EM-raw
open EMSpace using (EM)

-- Proposition 10. Connectivity of K(G,n)
open EMProps using (isConnectedEM)

-- Lemma 11.
open EMProps using (EMFun-EM→ΩEM+1)

--- 3.1 Group Structure
-- Proposition 12. (Wedge connectivity for K(G,n))
open WC.wedgeConEM using (fun ; left ; right)

-- Proposition 13. (unit laws for +ₖ)
open EMGr using (rUnitₖ ; lUnitₖ)
lUnit≡rUnit : ∀ {ℓ} {G : AbGroup ℓ} (n : ℕ)
  → rUnitₖ {G = G} n (EMSpace.0ₖ n) ≡ lUnitₖ {G = G} n (EMSpace.0ₖ n)
lUnit≡rUnit {G = G} zero = AbGroupStr.is-set (snd G) _ _ _ _
lUnit≡rUnit (suc zero) = refl
lUnit≡rUnit (suc (suc n)) = refl

-- Proposition 14. (commutativity of +ₖ)
open EMGr using (commₖ)

-- Proposition 15. (associativity of +ₖ)
open EMGr using (assocₖ)

-- Proposition 16. (ap² on +ₖ)
open EMGr using (cong₂+₁ ; cong₂+₂)

-- Proposition 17. (cancellation laws of +ₖ)
open EMGr using (rCancelₖ ; lCancelₖ)

--- 3.2 K(Gn) vs ΩK(G,n+1)
-- Proposition 18. Commutativity of Ω(K(G,n),x)
open EMProps using (isCommΩEM-base)

-- Proposition 19. (ap -ₖ = path inversion)
open EMGr using (cong-₁ ; cong-₂)

-- Proposition 20. (σ preserves +ₖ)
open EMProps using (EM→ΩEM+1-hom)

-- Corollary 21. (σ preserves -ₖ)
open EMProps using (EM→ΩEM+1-sym)

-- Theorem 22. K(G,n) ≃ Ω(K(G,n+1))
open EMProps using (EM≃ΩEM+1)

--- 3.3 The cup product with group coefficients
-- Definition 23. Tensor products of abelian groups
open Tensor using (_⨂_)

-- Proposition 24. Truncation of K(G,n) →* K(H;n+m)
open EMProps using (isOfHLevel↑∙)

-- The general cup product
open Cup⊗ renaming (_⌣ₖ_ to _⌣ₖ⊗_)

-- Proposition 25 (anihilation laws)
open Cup⊗ using (⌣ₖ-0ₖ ; 0ₖ-⌣ₖ)

-- Lemma 26 (Evan's trick)
open Homogeneous using (→∙Homogeneous≡)

-- Propositions 27 and 28 (distributivity of ⌣ₖ)
open Cup⊗.LeftDistributivity using (main)
open Cup⊗.RightDistributivity using (main)

-- Lemma 29
open Cup⊗ using (EM→ΩEM+1-distr₀ₙ ; EM→ΩEM+1-distrₙsuc ; EM→ΩEM+1-distrₙ₀)

-- Proposition 30 (associativity of ⌣ₖ)
open Cup⊗.Assoc using (main)

-- Proposition 31 (graded commutativity of CupComm)
open CupComm using (⌣ₖ-comm)

--- 3.4 The cup product with ring coefficients
-- Proposition 32 (ring structure on ⌣ₖ with ring coefficents)
open Cupₖ using (assoc⌣ₖ ; distrL⌣ₖ ; distrR⌣ₖ ; ⌣ₖ-0ₖ ; 0ₖ-⌣ₖ)

-- Proposition 33 (graded commutativity)
open Cupₖ using (⌣ₖ-comm)

-- Proposition 34 (neutral element)
open Cupₖ using (⌣ₖ-1ₖ ; 1ₖ-⌣ₖ)


----- 4. Cohomology -----
-- Defininition of cohomology groups
open Cohom using (coHomGr)

-- Cup products on cohomology
open CohomCup using (_⌣_)

--- 4.1 Reduced cohomology
-- Definition of reduced cohomology groups
open Cohom using (coHomRedGr)

-- Proposition 35.
open Cohom using (coHom≅coHomRed)

-- Proposition 36.
open Cohom using (coHom⁰≅coHomRed⁰)

--- 4.2 Eilenberg-Steenrod axioms for cohomology
-- Definition 37. Cofibres
open Pushouts using (cofib)

-- Definition 38. Arbitrary wedges
open ⋁ using (⋁gen)

-- Definition 39. Choice
open Choice using (satAC)

-- Definition 40. Eilenberg-Steenrod axioms
open Axioms using (coHomTheoryGen)

-- Theorem 41. Eilenberg-Steenrod axioms are satified
open SatAxioms using (satisfies-ES-gen)

-- Theorem 42 (The mayer-Vietoris sequence)
open MV.MV using ( Ker-i⊂Im-d ; Im-d⊂Ker-i
                 ; Ker-Δ⊂Im-i ; Im-i⊂Ker-Δ
                 ; Ker-d⊂Im-Δ ; Im-Δ⊂Ker-d)

--- 4.4 The Thom isomorphism and the Gysin sequence
-- Theorem 43 (Gysin sequence)
open Gysin.Gysin using ( Im-mapᵣ⊂Ker-mapₗ ; Ker-mapₗ⊂Im-mapᵣ
                       ; Ker-⌣⊂Im-mapₗ ; Im-mapₗ⊂Ker-⌣
                       ; Im--⌣⊂Ker-mapᵣ ; Ker-mapᵣ⊂Im--⌣)

--- 5. Computations of cohomology groups and rings
-- Proposition 44. Cohom of 1
open HⁿUnit using (H⁰[Unit,G]≅G ; Hⁿ⁺¹[Unit,G]≅0)

-- Lemma 45. Cohom of truncation
open Cohom using (coHomTruncEquiv)

-- Proposition 46. Cohomology of connected types
open CohomConnected using (H⁰conn)

--- 5.1 Speres
-- Proposition 47. H¹(S¹,G)
open CohomSn using (H¹[S¹,G]≅G)

-- Proposition 48. Hⁿ(Sⁿ,G)
open CohomSn using (Hⁿ[Sⁿ,G]≅G)

-- Proposition 49. Hⁿ(Sᵐ,G) , m ≠ n
open CohomSn using (Hⁿ[Sᵐ⁺ⁿ,G]≅0 ; Hᵐ⁺ⁿ[Sⁿ,G]≅0)

-- Proposition 50. H*(Sᵐ,G)
open CohomRingSn using (H*[Sⁿ,G]≅G[X]/<X²>)

--- 5.2 The Torus
-- Definition 51. Torus
open T² using (Torus)

-- Proposition 52. Hⁿ(T²,G)
open CohomT² using (H⁰[T²,G]≅G ; H¹[T²,G]≅G×G ; H²[T²,G]≅G ; H³⁺ⁿ[T²,G]≅0)

--- 5.3 The Real Projective Plane and The Klein Bottle
-- Definition 53. Real Projective Plane
open RP² using (RP²)
-- Definition 54. The Klein Bottle
open K² using (KleinBottle)

-- Proposition 55 H¹(RP²,G) ≅ G[2]
open CohomRP² using (H¹[RP²,G]≅G[2])

-- Proposition 56 H²(RP²,G) ≅ G/2
open CohomRP² using (H²[RP²,G]≅G/2)

-- Proposition 57 Hᵐ(RP²,G) ≅ 0, m ≥ 3
open CohomRP² using (H³⁺ⁿ[RP²,G]≅0)

-- Proposition 58. Hᵐ(K²,G)
open CohomK² using (H⁰[K²,G]≅G ; H¹[K²,G]≅G×H¹[RP²,G]; H²⁺ⁿ[K²,G]≅H²⁺ⁿ[RP²,G])

-- Proposition 59. H*(RP²,\bZ) -- Formalisation taken from `Computing Cohomology Rings in Cubical Agda'
open ZCohomRingRP² using (RP²-CohomologyRing)

-- Defnition 60 kill-Δ
-- Omitted (implicit in formalisation)

-- Proposition 61 H*(K²,ℤ) -- Formalisation taken from `Computing Cohomology Rings in Cubical Agda'
open ZCohomRingK² using (CohomologyRing-𝕂²)

-- Definition 62. Res (only formliased for relevant special case of F = ⌣ on K(ℤ/2,1))
open K²Ring using (Res⌣)

-- Propsoiton 63. Res refl = refl
-- omitted (used implicitly in formalisation)

-- Lemma 64/65. ap2-funct ocherence (this is roughly the special case of lemma 61)
open K²Ring using (sym-cong₂-⌣≡)

-- Proposition 66. Implicitly formalised via the following theorem
open K²Ring using (α²↦1)

-- Proposition 67. H*(RP²,Z/2)
open RP²Ring using (H*[RP²,ℤ₂]≅ℤ₂[X]/<X³>)

-- Proposition 68. (Roughly)
open K²Ring using (α²↦1 ; βα↦1 ; β²↦0)

-- Proposition 69. H*(K²,ℤ/2)
open K²Ring using (H*KleinBottle≅ℤ/2[X,Y]/<X³,Y²,XY+X²>)

-- Lemma 70. (implicitly used)

-- Proposition 71. H*(RP∞, ℤ/2)
open RP∞Ring using (H*[RP∞,ℤ₂]≅ℤ₂[X])

{-
Please do not move this file. Changes should only be made if
necessary.

This file contains pointers to the code examples and main results from
the paper:

  Formalising and computing the fourth homotopy group of the 3-sphere in Cubical Agda
-}

-- The "--safe" flag ensures that there are no postulates or
-- unfinished goals
{-# OPTIONS --cubical #-}

module Cubical.Papers.Pi4S3-JournalVersion where

-- Misc.
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order

-- 2
open import Cubical.Data.Bool as Boolean
open import Cubical.Data.Unit as UnitType

open import Cubical.HITs.S1 as Circle
open import Cubical.Foundations.Prelude                      as Prelude
open import Cubical.HITs.Susp                                as Suspensions
open import Cubical.HITs.Sn                                  as Spheres
  hiding (S) renaming (S₊ to S)
open import Cubical.HITs.Pushout                             as Pushouts
open import Cubical.HITs.Wedge                               as Wedges
open import Cubical.HITs.Join                                as Joins
open import Cubical.HITs.Susp                                as Suspension
open import Cubical.HITs.PropositionalTruncation             as PT
open import Cubical.HITs.Truncation                          as Trunc
open import Cubical.Foundations.Univalence                   as Univ
open import Cubical.Homotopy.Loopspace                       as Loopy

open import Cubical.Homotopy.HSpace                          as H-Spaces
open import Cubical.Homotopy.Group.Base                      as HomotopyGroups
open import Cubical.Homotopy.Group.LES                       as LES
open import Cubical.Homotopy.HopfInvariant.HopfMap           as HopfMap
open import Cubical.Homotopy.Hopf                            as HopfFibration
open import Cubical.Homotopy.Connected                       as Connectedness
open S¹Hopf
open import Cubical.Homotopy.Freudenthal                     as Freudenthal
open import Cubical.Homotopy.Group.PinSn                     as Stable
open import Cubical.Homotopy.Group.Pi3S2                     as π₃S²

-- 3
open import Cubical.Homotopy.Group.Pi4S3.S3PushoutIso        as James₁
open import Cubical.Homotopy.Group.Pi4S3.S3PushoutIso2       as James₂
open import Cubical.HITs.S2                                  as Sphere
open import Cubical.Homotopy.Whitehead                       as Whitehead
open import Cubical.Homotopy.BlakersMassey
module BM = BlakersMassey□
open BM
open import Cubical.Homotopy.Group.Pi4S3.BrunerieNumber      as BNumber
  hiding (W)

-- 5
open import Cubical.ZCohomology.Base                         as cohom
open import Cubical.ZCohomology.GroupStructure               as cohomGr
open import Cubical.ZCohomology.Properties                   as cohomProps
open import Cubical.ZCohomology.RingStructure.CupProduct     as cup
open import Cubical.ZCohomology.MayerVietorisUnreduced       as MayerVietoris
open import Cubical.Homotopy.HopfInvariant.Base              as HI
open import Cubical.Homotopy.HopfInvariant.Homomorphism      as HI-hom
open import Cubical.Homotopy.HopfInvariant.Brunerie          as HI-β
open import Cubical.ZCohomology.Gysin                        as GysinSeq
open import Cubical.Homotopy.Group.Pi4S3.Summary             as π₄S³
  hiding (π)
open import Cubical.ZCohomology.RingStructure.RingLaws       as cupLaws

-- 6
open import Cubical.HITs.SmashProduct.Base                   as SmashProd
open import Cubical.HITs.Sn.Multiplication                   as SMult
open import Cubical.Homotopy.Group.Join                      as JoinGroup
open import Cubical.Homotopy.Group.Pi4S3.DirectProof         as Direct


------ 2. HOMOTOPY TYPE THEORY IN Cubical Agda ------

--- 2.1 Elementary HoTT notions and Cubical Agda notations ---

-- Booleans
open Boolean using (Bool)

-- Unit
open UnitType renaming (Unit to 𝟙)

-- S¹
open Circle using (S¹)

-- Non-dependent paths and refl
open Prelude using (_≡_ ; refl)

-- funExt, funExt⁻, cong
open Prelude using (funExt; funExt⁻; cong)

-- PathP
open Prelude using (PathP)

-- cirlce-indution
open Circle using (elim)

--- 2.2 More higher inductive types ---

-- suspension
open Suspensions using (Susp)

-- spheres
open Spheres using (S₊)

-- pushouts
open Pushouts using (Pushout)

-- wedge sums
open Wedges using (_⋁_)

-- joins
open Joins using (join)

-- cofibres
open Pushouts using (cofib)

-- ∇ and i∨
open Wedges using (fold⋁ ; ⋁↪)
∇ = fold⋁
i∨ = ⋁↪

--- 2.3 Truncation levels and n-truncations  ---

-- propositional and general truncation
-- note that the indexing is off by 2!
open PT using (∥_∥₁)
open Trunc using (∥_∥_)

--- 2.4 Univalence, loop spaces, and H-spaces ---

-- Univalence, ua
open Univ using (univalence ; ua)

-- Loop spaces
open Loopy using (Ω)

-- H-spaces
open H-Spaces using (HSpace)

------ 3. First results on homotopy groups of spheres ------

-- homotopy groups (function and loop space definition, respectively)
-- Note that the indexing is off by 1.
open HomotopyGroups using (π'Gr ; πGr)

-- Proposition 3.2 - Long exact sequence of homotoy groups
module ExactSeq = πLES

-- σ (definition 3.3)
open Suspensions renaming (toSusp to σ)

-- Proposition 3.4: Sⁿ * Sᵐ ≃ Sⁿ⁺ᵐ⁺¹
open SMult using (IsoSphereJoin)

-- Definition 3.5 and Proposition 3.6 (Hopf map),
-- Phrased somewhat differently in the paper.
open HopfMap using (HopfMap)
open S¹Hopf using (IsoS³TotalHopf)

-- Lemma 3.7 (connectedness of spheres)
-- Note that the indexing is off by 2.
open Spheres using (sphereConnected)

-- Proposition 3.8 (πₙSᵐ vanishishing for n < m)
isContr-πₙSᵐ-low : (n m : ℕ) → n < m → isContr (π n (S₊∙ m))
isContr-πₙSᵐ-low n m l =
  transport (cong isContr (sym (ua h)))
     (∣ const∙ (S₊∙ n) _ ∣₂
     , ST.elim (λ _ → isOfHLevelPath 2 squash₂ _ _)
       λ f → refl)
  where
  open import Cubical.HITs.SetTruncation as ST
  con-lem : isConnected (2 + n) (S₊ m)
  con-lem = isConnectedSubtr (suc (suc n)) (fst l)
             (subst (λ n → isConnected n (S₊ m))
               (sym (+-suc (fst l) (suc n) ∙ cong suc (snd l)))
                (sphereConnected m))

  h : π n (S₊∙ m) ≃ π' n (Unit , tt)
  h = compEquiv (isoToEquiv (πTruncIso n))
       (compEquiv (pathToEquiv (cong (π n)
          (ua∙ (isoToEquiv (isContr→Iso (con-lem) isContrUnit)) refl)))
          (pathToEquiv (cong ∥_∥₂ (isoToPath (IsoΩSphereMap n)))))

-- Theorem 3.9 (Freudenthal Suspension Theorem)
open Freudenthal using (isConnectedσ) -- formalized by Evan Cavallo

-- Corollary 3.10 (πₙSⁿ≅ℤ with identity as generator)
open Stable using (πₙ'Sⁿ≅ℤ ; πₙ'Sⁿ≅ℤ-idfun∙)

-- Proposition 3.11 and Corollary 3.12 (π₃S²≅ℤ with Hopf map as generator)
open π₃S² using (π₃S²≅ℤ ; π₂S³-gen-by-HopfMap)

------ 4. THE BRUNERIE NUMBER ------
{- The formalisation of this part does not
follow the paper exactly. For this reason, we only give
the crucial results here -}

--- 4.1 The James construction ---
-- Expository section only. No formalisation following this part of
-- the paper.

--- 4.2 The James construction ---

-- Lemma 3 (the family of automorphisms on ∥J₂S²∥₃
open James₁ using (∥Pushout⋁↪fold⋁S²∥₅≃∥Pushout⋁↪fold⋁S²∥₅)


---- B. Formalization of the James construction ----

-- Definition 4.4: J₂S²
open James₁ using (Pushout⋁↪fold⋁S₊2)

-- S²-HIT
open Sphere using (S²)

-- Lemma 4.5
-- Omitted (used implicitly)

-- Lemma 4.6 (the family of automorphisms on ∥J₂S²∥₃
open James₁ using (∥Pushout⋁↪fold⋁S²∥₅≃∥Pushout⋁↪fold⋁S²∥₅)

-- Proposition 4.7: Ω ∥S³∥₄ ≃ ∥J₂S²∥₃
open James₁ using (IsoΩ∥SuspS²∥₅∥Pushout⋁↪fold⋁S²∥₅)


--- 4.3. Definition of the Brunerie number ---

-- Definition 4.8: W + whitehead product
W = joinTo⋁
open Whitehead using ([_∣_])

-- Theorem 4.9 is omitted as it is used implicitly in the proof of the main result

-- Theorem 4.10 Blakers-Massey
open BM using (isConnected-toPullback) -- formalized primarily (in a different form) by Kang Rongji

-- Definition 4.11: The Brunerie number (note that, in the formalization
-- we have worked defined β as the image of the Hopf Invariant
-- directly)
open BNumber using (Brunerie)

-- Corollary 4.12: π₄S³ ≅ ℤ/βℤ
open BNumber using (BrunerieIso)


------ 5. BRUNERIE'S PROOF THAT |β| ≡ 2 ------

---- A. Cohomology Theory / B. Formalization of Chapter 5----
-- All formalizations marked with (BLM22) are borrowed from Brunerie,
-- Ljungström, and Mörtberg, “Synthetic Integral Cohomology in Cubical
-- Agda"

--- 5.1 Cohomology and the Hopf invariant ---

-- Eilenberg-MacLane spaces and cohomology groups (BLM22)
open cohom using (coHomK)
open cohomGr using (coHomGr)

-- addition (BLM22)
open cohomGr using (_+ₖ_)

-- the cup product (BLM22)
open cup using (_⌣ₖ_ ; _⌣_)

-- Kₙ ≃ ΩKₙ₊₁ (BLM22)
open cohomProps using (Kn≃ΩKn+1)

-- Mayer Vietoris (BLM22)
open MV using ( Ker-i⊂Im-d ; Im-d⊂Ker-i
              ; Ker-Δ⊂Im-i ; Im-i⊂Ker-Δ
              ; Ker-d⊂Im-Δ ; Im-Δ⊂Ker-d)

-- Lemma 5.1 (cohomology of cofibers S³ → S²)
open HI using (Hopfβ-Iso)

-- Definition 5.2 (Hopf Invariant)
open HI using (HopfInvariant-π')

-- Proposition 5.3 (The Hopf invariant is a homomorphism)
open HI-hom using (GroupHom-HopfInvariant-π')

-- Proposition 5.4 (The Hopf invariant of the Brunerie element is ±2)
open HI-β using (Brunerie'≡2)

-- Lemma 5.5 -- only included for presentation, omitted from frmalization

--- 5.1 The Gysin sequence ---

-- Proposition 5.6 (Gysin sequence)
open Gysin using (Im-⌣e⊂Ker-p ; Ker-p⊂Im-⌣e
                ; Im-Susp∘ϕ⊂Ker-⌣e ; Ker-⌣e⊂Im-Susp∘ϕ
                ; Im-ϕ∘j⊂Ker-p ; Ker-p⊂Im-ϕ∘j)

-- Proposition 5.7 : CP² fibration
-- Indirect, but see in particular
open HopfMap using (fibr)

-- Proposition 5.8 : Iterated Hopf Construction.
-- Indirect, but see in particular:
open Hopf using (joinIso₂)

-- Proposition 5.9 : ∣ HI hopf ∣ ≡ 1
open HopfMap using (HopfInvariant-HopfMap)

-- Theorem 5.10: π₄S³≅ℤ/2ℤ
open π₄S³ using (π₄S³≃ℤ/2ℤ)

--- Formalisation of the Gysin sequence. ---
-- Lemma 5.11: (BLM22)
open cupLaws using (assoc-helper)

-- proof that e₂ : H²(CP²) is a generator by computation
-- (the field with refl is where the computation happens)
open HopfMap using (isGenerator≃ℤ-e)

------ 6. THE SIMPLIFIED NEW PROOF AND NORMALISATION OF A BRUNERIE NUMBER ------

--- 6.1. Interlude: joins and smash products of spheres ---

-- Smash product (not defined as an implicit HIT)
open SmashProd using (_⋀_)

-- Lemmas 6.1 and 6.2
-- Omitted (included for presentation purposes, not used explicitly in
-- formalisation)

-- Definition of pinch map
open SmashProd renaming (Join→SuspSmash to pinch)

-- Proposition 6.3 (pinch is an equivalence)
open SmashProd using (SmashJoinIso)

-- Definition of Fₙₘ
open SMult renaming (join→Sphere to F)

-- Proposition 6.4 (Fₙ,ₘ is an equivalence)
open SMult using (IsoSphereJoin)

-- Propositions 6.5 & 6.6 (graded commutativity and associativity)
open SMult using (comm⌣S ; assoc⌣S)

--- 6.2. Homotopy groups in terms of joins.

-- Definition 6.7
open JoinGroup using (π*)

-- Addition +*
open JoinGroup using (_+*_)

-- Proposition 6.8
open JoinGroup using (·Π≡+*)

-- Proposition 6.9
open JoinGroup using (π*Gr≅π'Gr)

-- Proposition 6.10
open JoinGroup using (π*∘∙Hom)

--- 6.3. The new synthetic proof that π₄(S³) ≅ ℤ/2ℤ
-- A relatively detailed accound of the proof is given in the formalisation:
open Direct
-- Note that the numbering of the ηs is shifted, with
-- η₁ being ∣ ∇ ∘ W ∣, η₂ being η₁ and η₃ being η₂.
open Direct using (η₁ ; η₂ ; η₃)

-- computation of η₂: the alternative definition and the computation
open Direct using (η₃' ; computerIsoη₃)

--- 6.4. A stand-alone proof of Brunerie’s theorem?
-- Theorem 6.18
-- Not formalised explicitly

-- Definition of generalised Whitehead products ·w
open Whitehead using (_·w_)

-- Proposition 6.22 (including Lemmas 19 and 20 and Proposition 6.21)
open Whitehead using (isConst-Susp·w)

-- Theorem 6.23
-- Follows directly from above but not formalised explicitly (awaiting
-- refactoring of some code in the library)

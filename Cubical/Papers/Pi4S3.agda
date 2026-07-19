{-
Please do not move this file. Changes should only be made if
necessary.

This file contains pointers to the code examples and main results from
the paper:

Formalizing π₄(S³) ≅ ℤ/2ℤ and Computing a Brunerie Number in Cubical Agda

-}

-- The "--safe" flag ensures that there are no postulates or
-- unfinished goals
{-# OPTIONS --cubical #-}

module Cubical.Papers.Pi4S3 where

-- Misc.
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.HLevels

open import Cubical.Data.Int hiding (_+_)
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sum
open import Cubical.Data.Sigma

-- 2
open import Cubical.Data.Bool as Boolean
open import Cubical.HITs.S1 as Circle
open import Cubical.Foundations.Prelude                     as Prelude
open import Cubical.HITs.Susp                               as Suspensions
open import Cubical.HITs.Sn                                 as Spheres
  hiding (S) renaming (S₊ to S)
open import Cubical.HITs.Sn.Multiplication                  as SMult
open import Cubical.HITs.Pushout                            as Pushouts
open import Cubical.HITs.Wedge                           as Wedges
open import Cubical.HITs.Join                               as Joins
open import Cubical.HITs.Susp                               as Suspension
open import Cubical.HITs.PropositionalTruncation             as PT
open import Cubical.HITs.Truncation                         as Trunc
open import Cubical.Homotopy.HSpace                         as H-Spaces
open import Cubical.Homotopy.Group.Base                     as HomotopyGroups
open import Cubical.Homotopy.Group.LES                      as LES
open import Cubical.Homotopy.HopfInvariant.HopfMap          as HopfMap
open import Cubical.Homotopy.Hopf                           as HopfFibration
open import Cubical.Homotopy.Connected                      as Connectedness
open S¹Hopf
open import Cubical.Homotopy.Freudenthal                    as Freudenthal
open import Cubical.Homotopy.Group.PinSn                    as Stable
open import Cubical.Homotopy.Group.Pi3S2                    as π₃S²

-- 3
open import Cubical.Homotopy.Group.Pi4S3.S3PushoutIso       as James₁
open import Cubical.Homotopy.Group.Pi4S3.S3PushoutIso2      as James₂
open import Cubical.HITs.S2                                 as Sphere
open import Cubical.Homotopy.Whitehead                      as Whitehead
open import Cubical.Homotopy.BlakersMassey
module BM = BlakersMassey□
open BM
open import Cubical.Homotopy.Group.Pi4S3.BrunerieNumber      as BNumber
  hiding (W)

-- 5
open import Cubical.ZCohomology.Base                         as cohom
open import Cubical.ZCohomology.GroupStructure               as cohomGr
open import Cubical.ZCohomology.Properties              as cohomProps
open import Cubical.ZCohomology.RingStructure.CupProduct     as cup
open import Cubical.ZCohomology.MayerVietorisUnreduced       as MayerVietoris
open import Cubical.Homotopy.HopfInvariant.Base              as HI
open import Cubical.Homotopy.HopfInvariant.Homomorphism      as HI-hom
open import Cubical.Homotopy.HopfInvariant.Brunerie          as HI-β
open import Cubical.ZCohomology.Gysin                        as GysinSeq
open import Cubical.Homotopy.Group.Pi4S3.Summary              as π₄S³
  hiding (π)
open import Cubical.ZCohomology.RingStructure.RingLaws       as cupLaws

-- 6
open import Cubical.Homotopy.Group.Pi4S3.DirectProof              as Direct

-- II. HOMOTOPY TYPE THEORY IN Cubical Agda
-- Booleans
open Boolean using (Bool)

-- S¹
open Circle using (S¹)

-- Non-dependent paths and refl
open Prelude using (_≡_ ; refl)

-- funExt, funExt⁻, cong
open Prelude using (funExt; funExt⁻; cong)

-- transport and dependent paths
open Prelude using (transport ; PathP)

-- cirlce-indution
open Circle using (elim)

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

-- propositional and general truncation
-- note that the indexing is off by 2!
open PT using (∥_∥₁)
open Trunc using (∥_∥_)

-- h-spaces
open H-Spaces using (HSpace)

-- homotopy groups (function and loop space definition, respectively)
-- Note that the indexing is off by 1.
open HomotopyGroups using (π'Gr ; πGr)

-- πLES (Proposition 1)
module ExactSeq = πLES

-- σ (definition 3)
open Suspensions using (toSusp)
σ = toSusp

-- Definition 4 and Proposition (Hopf map),
-- Phrased somewhat differently in the paper.
open HopfMap using (HopfMap)
open S¹Hopf using (IsoS³TotalHopf)

-- Lemma 1 (connectedness of spheres)
-- Note that the indexing is off by 2.
open Spheres using (sphereConnected)

-- Proposition 3 (πₙSᵐ vanishishing for n < m)
isContr-πₙSᵐ-low : (n m : ℕ) → n < m → isContr (π n (S₊∙ m))
isContr-πₙSᵐ-low n m l =
  transport (cong isContr (sym (ua h)))
     (∣ const∙ (S₊∙ n) _ ∣₂
     , ST.elim (λ _ → isOfHLevelPath 2 squash₂ _ _)
       λ f → refl)
  where
  open import Cubical.HITs.SetTruncation as ST
  isContrUnit : isContr Unit
  isContrUnit = tt , λ _ → refl

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

-- Theorem 1 (Freudenthal Suspension Theorem)
open Freudenthal using (isConnectedσ) -- formalized by Evan Cavallo

-- Corollary 1 (πₙSⁿ≅ℤ with identity as generator)
open Stable using (πₙ'Sⁿ≅ℤ ; πₙ'Sⁿ≅ℤ-idfun∙)

-- Proposition 4 and Corollary 2 (πₙSⁿ≅ℤ with identity as generator)
open π₃S² using (π₃S²≅ℤ ; π₂S³-gen-by-HopfMap)


------ IV. THE BRUNERIE NUMBER ------
{- The formalization of this part does not
follow the paper exactly. For instance, Lemma 2 is baked into a more
specific elimination principle for J₂. For this reason, we only give
the crucial results here -}

---- A. The James construction ----

-- Lemma 3 (the family of automorphisms on ∥J₂S²∥₃
open James₁ using (∥Pushout⋁↪fold⋁S²∥₅≃∥Pushout⋁↪fold⋁S²∥₅)


---- B. Formalization of the James construction ----

-- S²-HIT
open Sphere using (S²)

-- Definition 5: J₂S²
open James₁ using (Pushout⋁↪fold⋁S₊2)

-- encode, decode
open James₁ using (encode ; decode)

-- Proposition 7: Ω ∥S³∥₄ ≃ ∥J₂S²∥₃
open James₁ using (IsoΩ∥SuspS²∥₅∥Pushout⋁↪fold⋁S²∥₅)

---- C. Formalization of the James construction ----
-- Proposition 8: Sⁿ * Sᵐ ≃ Sⁿ⁺ᵐ⁺¹
open SMult using (IsoSphereJoin)

-- Definition 6: W + whitehead product
W = joinTo⋁
open Whitehead using ([_∣_])

-- Theorem 3 is omitted as it is used implicitly in the proof of the main result

-- Blakers-Massey
open BM using (isConnected-toPullback) -- formalized primarily (in a different form) by Kang Rongji

-- Definition 7: The Brunerie number (note that, in the formalization
-- we have worked defined β as the image of the Hopf Invariant
-- directly)
open BNumber using (Brunerie)

-- Corollary 3: π₄S³ ≅ ℤ/βℤ
open BNumber using (BrunerieIso)

---

------ V. BRUNERIE'S PROOF PART 2 ------

---- A. Cohomology Theory / B. Formalization of Chapter 5----
-- All formalizations marked with (BLM22) are borrowed from Brunerie,
-- Ljungström, and Mörtberg, “Synthetic Integral Cohomology in Cubical
-- Agda"

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

-- Lemma 4 (cohomology of cofibers S³ → S²)
open HI using (Hopfβ-Iso)

-- Definition 8 (Hopf Invariant)
open HI using (HopfInvariant-π')

-- Proposition 9 (The Hopf invariant is a homomorphism)
open HI-hom using (GroupHom-HopfInvariant-π')

-- Proposition 10 (The Hopf invariant of the Brunerie element is ±2)
open HI-β using (Brunerie'≡2)

-- Lemma 5 -- only included for presentation, omitted from frmalization

---- C. The Gysin Sequence / B. Formalization of the Gysin Sequence

-- Proposition 11 (Gysin sequence)
open Gysin using (Im-⌣e⊂Ker-p ; Ker-p⊂Im-⌣e
                ; Im-Susp∘ϕ⊂Ker-⌣e ; Ker-⌣e⊂Im-Susp∘ϕ
                ; Im-ϕ∘j⊂Ker-p ; Ker-p⊂Im-ϕ∘j)

-- Proposition 12 : CP² fibration
-- Indirect, but see in particular
open HopfMap using (fibr)

-- Proposition 13 : Iterated Hopf Construction.
-- Indirect, but see in particular:
open Hopf using (joinIso₂)

-- Proposition 14 : ∣ HI hopf ∣ ≡ 1
open HopfMap using (HopfInvariant-HopfMap)

-- Theorem 5: π₄S³≅ℤ/2ℤ
open π₄S³ using (π₄S³≃ℤ/2ℤ)

-- Lemma 6: (BLM22)
open cupLaws using (assoc-helper)

-- proof that e₂ : H²(CP²) is a generator by computation
-- (the field with refl is where the computation happens)
open HopfMap using (isGenerator≃ℤ-e)

------ VI. SIMPLIFIED NEW PROOF AND COMPUTATION OF A BRUNERIE NUMBER ------
-- A relatively detailed accound of the proof is given in the formalization:
open Direct
-- Note that the numbering of the ηs is shifted, with
-- η₁ being ∣ ∇ ∘ W ∣, η₂ being η₁ and η₃ being η₂.
open Direct using (η₁ ; η₂ ; η₃)

-- computation of η₂: the alternative definition and the computation
open Direct using (η₃' ; computerIsoη₃)

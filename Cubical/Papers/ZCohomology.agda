{-

Please do not move this file. Changes should only be made if
necessary.

This file contains pointers to the code examples and main results from
the paper:

Synthetic Cohomology Theory in Cubical Agda

-}

-- The "--safe" flag ensures that there are no postulates or
-- unfinished goals
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Papers.ZCohomology where

-- Misc.
open import Cubical.Data.Int hiding (_+_)
open import Cubical.Data.Nat
open import Cubical.Foundations.Everything
open import Cubical.HITs.S1
open import Cubical.Data.Sum

-- II
import Cubical.Foundations.Prelude                   as Prelude
import Cubical.Foundations.GroupoidLaws              as GroupoidLaws
import Cubical.Foundations.Path                      as Path
open import Cubical.HITs.S1                          as S1
open import Cubical.HITs.Susp                        as Suspension
open import Cubical.HITs.Sn                          as Sn
open import Cubical.Homotopy.Loopspace               as Loop
open import Cubical.Foundations.HLevels              as n-types
open import Cubical.Homotopy.Connected               as Connected
import Cubical.HITs.Pushout                          as Push
import Cubical.HITs.Wedge                            as ⋁
import Cubical.Foundations.Univalence                as Unival
import Cubical.Foundations.SIP                       as StructIdPrinc
import Cubical.Algebra.Group                         as Gr

-- III
import Cubical.ZCohomology.Base                      as coHom
  renaming (coHomK to K)
import Cubical.HITs.Sn.Properties                    as S
import Cubical.ZCohomology.GroupStructure            as GroupStructure
import Cubical.ZCohomology.Properties                as Properties
  renaming (Kn→ΩKn+1 to σ ; ΩKn+1→Kn to σ⁻¹)
import Cubical.Experiments.ZCohomologyOld.Properties as oldCohom

-- IV
import Cubical.Homotopy.EilenbergSteenrod            as ES-axioms
import Cubical.ZCohomology.EilenbergSteenrodZ        as satisfies-ES-axioms
  renaming (coHomFunctor to H^~ ; coHomFunctor' to Ĥ)
import Cubical.ZCohomology.MayerVietorisUnreduced    as MayerVietoris

-- V
import Cubical.ZCohomology.Groups.Sn                 as HⁿSⁿ
  renaming (Hⁿ-Sᵐ≅0 to Hⁿ-Sᵐ≅1)
import Cubical.ZCohomology.Groups.Torus              as HⁿT²
import Cubical.ZCohomology.Groups.Wedge              as Hⁿ-wedge
import Cubical.ZCohomology.Groups.KleinBottle        as Hⁿ𝕂²
import Cubical.ZCohomology.Groups.RP2                as HⁿℝP²
  renaming (H¹-RP²≅0 to H¹-RP²≅1)

----- II. HOMOTOPY TYPE THEORY IN CUBICAL AGDA -----

-- II.A Important notions in Cubical Agda
open Prelude using ( PathP
                   ; _≡_
                   ; refl
                   ; cong
                   ; funExt)

open GroupoidLaws using (_⁻¹)

open Prelude using ( transport
                   ; subst
                   ; hcomp)

--- II.B Important concepts from HoTT/UF in Cubical Agda

-- The circle, 𝕊¹
open S1 using (S¹)

-- Suspensions
open Suspension using (Susp)

-- n-spheres, 𝕊ⁿ
open Sn using (S₊)

-- Loop spaces
open Loop using (Ω^_)

-- Eckmann-Hilton argument
open Loop using (Eckmann-Hilton)

-- n-types Note that we start indexing from 0 in the Cubical Library
-- (so (-2)-types as referred to as 0-types, (-1) as 1-types, and so
-- on)
open n-types using (isOfHLevel)

-- Connectedness
open Connected using (isConnected)

-- Pushouts
open Push using (Pushout)

-- Wedge sum
open ⋁ using (_⋁_)


-- III.C Univalence

-- Univalence and the ua function respectively
open Unival using (univalence ; ua)

-- The structure identity principle and the sip function
-- respectively
open StructIdPrinc using (SIP ; sip)

-- Groups
open Gr using (Group)


----- III. ℤ-COHOMOLOGY IN CUBICAL AGDA -----


-- III.A Eilenberg-MacLane spaces

-- Eilenberg-MacLane spaces Kₙ
open coHom using (K)

-- Proposition 1
open S using (sphereConnected)

-- Lemma 1
open S using (wedgeConSn)

-- The proof of p ≡ (left *)⁻¹ ∙ (right *) is not explicitly stated in
-- the library since it is so trivial. We give it here instead.
left-right-hom : ∀ {ℓ} (n m : ℕ) {A : (S₊ (suc n)) → (S₊ (suc m)) → Type ℓ}
          → (hlev : ((x : S₊ (suc n)) (y : S₊ (suc m)) → isOfHLevel ((suc n) + (suc m)) (A x y)))
          → (f : (x : _) → A (ptSn (suc n)) x)
          → (g : (x : _) → A x (ptSn (suc m)))
          → (p : g (ptSn (suc n)) ≡ f (ptSn (suc m)))
          → p ≡ sym (S.wedgeConSn n m hlev f g p .snd .snd (ptSn (suc n)))
               ∙ S.wedgeConSn n m hlev f g p .snd .fst (ptSn (suc m))
left-right-hom zero zero hlev f g p = rUnit p
left-right-hom zero (suc m) hlev f g p = lUnit p
left-right-hom (suc n) m hlev f g p = rUnit p

-- We cannot state the definitional equality explicitly, but the following
-- makes sure that these hold definitionally (as they're proved by refl)
defEq : ∀ {ℓ} (n m : ℕ) {A : (S₊ (suc n)) → (S₊ (suc m)) → Type ℓ}
          → (hlev : ((x : S₊ (suc n)) (y : S₊ (suc m)) → isOfHLevel ((suc n) + (suc m)) (A x y)))
          → (f : (x : _) → A (ptSn (suc n)) x)
          → (g : (x : _) → A x (ptSn (suc m)))
          → (p : g (ptSn (suc n)) ≡ f (ptSn (suc m)))
          → (f ≡ S.wedgeConSn n m hlev f g p .fst (ptSn (suc n)))
          ⊎ (g ≡ λ x → S.wedgeConSn n m hlev f g p .fst x (ptSn (suc m)))
defEq zero zero hlev f g p = inl refl
defEq zero (suc m) hlev f g p = inr refl
defEq (suc n) m hlev f g p = inl refl

-- +ₖ (addition), -ₖ and 0ₖ
open GroupStructure using (_+ₖ_ ; -ₖ_ ; 0ₖ)

-- Group laws for +ₖ
open GroupStructure using ( rUnitₖ ; lUnitₖ
                          ; rCancelₖ ; lCancelₖ
                          ; commₖ
                          ; assocₖ)

-- All group laws are equal to refl at 0ₖ
-- rUnitₖ (definitional)
0-rUnit≡refl : rUnitₖ 0 (0ₖ 0) ≡ refl
1-rUnit≡refl : rUnitₖ 1 (0ₖ 1) ≡ refl
0-rUnit≡refl = refl
1-rUnit≡refl = refl
n≥2-rUnit≡refl : {n : ℕ} → rUnitₖ (2 + n) (0ₖ (2 + n)) ≡ refl
n≥2-rUnit≡refl = refl

-- rUnitₖ (definitional)
0-lUnit≡refl : lUnitₖ 0 (0ₖ 0) ≡ refl
1-lUnit≡refl : lUnitₖ 1 (0ₖ 1) ≡ refl
n≥2-lUnit≡refl : {n : ℕ} → lUnitₖ (2 + n) (0ₖ (2 + n)) ≡ refl
0-lUnit≡refl = refl
1-lUnit≡refl = refl
n≥2-lUnit≡refl = refl

-- assocₖ (definitional)
0-assoc≡refl : assocₖ 0 (0ₖ 0) (0ₖ 0) (0ₖ 0) ≡ refl
1-assoc≡refl : assocₖ 1 (0ₖ 1) (0ₖ 1) (0ₖ 1) ≡ refl
n≥2-assoc≡refl : {n : ℕ} → assocₖ (2 + n) (0ₖ (2 + n)) (0ₖ (2 + n)) (0ₖ (2 + n)) ≡ refl
0-assoc≡refl = refl
1-assoc≡refl = refl
n≥2-assoc≡refl = refl

-- commₖ (≡ refl ∙ refl for n ≥ 2)
0-comm≡refl : commₖ 0 (0ₖ 0) (0ₖ 0) ≡ refl
1-comm≡refl : commₖ 1 (0ₖ 1) (0ₖ 1) ≡ refl
n≥2-comm≡refl : {n : ℕ} → commₖ (2 + n) (0ₖ (2 + n)) (0ₖ (2 + n)) ≡ refl
0-comm≡refl = refl
1-comm≡refl = refl
n≥2-comm≡refl = sym (rUnit refl)

-- lCancelₖ (≡ refl ∙ transport refl refl for n = 1
--         and transport refl refl ∙ transport refl refl for n ≥ 2)
0-lCancel≡refl : lCancelₖ 0 (0ₖ 0) ≡ refl
1-lCancel≡refl : lCancelₖ 1 (0ₖ 1) ≡ refl
n≥2-lCancel≡refl : {n : ℕ} → lCancelₖ (2 + n) (0ₖ (2 + n)) ≡ refl
0-lCancel≡refl = refl
1-lCancel≡refl = sym (lUnit _) ∙ transportRefl refl
n≥2-lCancel≡refl = rCancel _

-- rCancelₖ (≡ transport refl refl for n ≥ 1)
0-rCancel≡refl : rCancelₖ 0 (0ₖ 0) ≡ refl
1-rCancel≡refl : rCancelₖ 1 (0ₖ 1) ≡ refl
n≥2-rCancel≡refl : {n : ℕ} → rCancelₖ (2 + n) (0ₖ (2 + n)) ≡ refl
0-rCancel≡refl = refl
1-rCancel≡refl = transportRefl refl
n≥2-rCancel≡refl = transportRefl refl

-- Proof that there is a unique h-structure on Kₙ
-- +ₖ defines an h-Structure on Kₙ
open GroupStructure using (_+ₖ_ ; 0ₖ ; rUnitₖ ; lUnitₖ ; lUnitₖ≡rUnitₖ)

-- and so does Brunerie's addition
open oldCohom using (_+ₖ_ ; 0ₖ ; rUnitₖ ; lUnitₖ ; rUnitlUnit0)

-- consequently both additions agree
open GroupStructure using (+ₖ-unique)
open oldCohom using (addLemma)
additionsAgree : (n : ℕ) → GroupStructure._+ₖ_ {n = n} ≡ oldCohom._+ₖ_ {n = n}
additionsAgree zero i x y = oldCohom.addLemma x y (~ i)
additionsAgree (suc n) i x y =
  +ₖ-unique n (GroupStructure._+ₖ_) (oldCohom._+ₖ_)
              (GroupStructure.rUnitₖ (suc n)) (GroupStructure.lUnitₖ (suc n))
              (oldCohom.rUnitₖ (suc n)) (oldCohom.lUnitₖ (suc n))
              (sym (lUnitₖ≡rUnitₖ (suc n)))
              (rUnitlUnit0 (suc n)) x y i

-- The function σ : Kₙ → ΩKₙ₊₁
open Properties using (σ)

-- Theorem 1 (Kₙ ≃ ΩKₙ₊₁)
open Properties using (Kn≃ΩKn+1)

-- σ and σ⁻¹ are morphisms
-- (for σ⁻¹ this is proved directly without using the fact that σ is a morphism)
open Properties using (Kn→ΩKn+1-hom ; ΩKn+1→Kn-hom)

-- Lemma 2 (p ∙ q ≡ cong²₊(p,q)) for n = 1 and n ≥ 2 respectively
open GroupStructure using (∙≡+₁ ; ∙≡+₂)

-- Lemma 3 (cong²₊ is commutative) and Theorem 2 respectively
open GroupStructure using (cong+ₖ-comm ; isCommΩK)

-- III.B Group structure on Hⁿ(A)

-- +ₕ (addition), -ₕ and 0ₕ
open GroupStructure using (_+ₕ_ ; -ₕ_ ; 0ₕ)

-- Cohomology group structure
open GroupStructure using ( rUnitₕ ; lUnitₕ
                          ; rCancelₕ ; lCancelₕ
                          ; commₕ
                          ; assocₕ)

-- Reduced cohomology, group structure
open GroupStructure using (coHomRedGroupDir)

-- Equality of unreduced and reduced cohmology
open Properties using (coHomGroup≡coHomRedGroup)


----- IV. THE EILENBERG-STEENROD AXIOMS -----

-- IV.A The axioms in HoTT/UF

-- The axioms are defined as a record type
open ES-axioms.coHomTheory

-- Proof of the claim that the alternative reduced cohomology functor
-- Ĥ is the same as the usual reduced cohomology functor
_ : ∀ {ℓ} → satisfies-ES-axioms.H^~ {ℓ} ≡ satisfies-ES-axioms.Ĥ
_ = satisfies-ES-axioms.coHomFunctor≡coHomFunctor'

-- IV.B Verifying the axioms

-- Propositions 2 and 3.
_ : ∀ {ℓ} → ES-axioms.coHomTheory {ℓ} satisfies-ES-axioms.H^~
_ = satisfies-ES-axioms.isCohomTheoryZ


-- III.C Characterizing Z-cohomology groups using the axioms

-- Theorem 3
open MayerVietoris.MV using ( Ker-i⊂Im-d ; Im-d⊂Ker-i
                            ; Ker-Δ⊂Im-i ; Im-i⊂Ker-Δ
                            ; Ker-d⊂Im-Δ ; Im-Δ⊂Ker-d)


----- V. CHARACTERIZING COHOMOLOGY GROUPS DIRECTLY -----

-- V.A
-- Proposition 4 and 5 respectively
open HⁿSⁿ using (Hⁿ-Sⁿ≅ℤ ; Hⁿ-Sᵐ≅1)

-- V.B
-- Proposition 6 and 7 respectively
open HⁿT² using (H¹-T²≅ℤ×ℤ ; H²-T²≅ℤ)

-- V.C
-- Proposition 8 and 9 respectively (Hⁿ(𝕂²))
-- ℤ/2ℤ is represented by Bool with the unique group structure
open Hⁿ𝕂² using (H¹-𝕂²≅ℤ ; H²-𝕂²≅Bool)

-- First and second cohomology groups of ℝP² respectively
open HⁿℝP² using (H¹-RP²≅1 ; H²-RP²≅Bool)




----- VI. COMPUTING WITH THE COHOMOLOGY GROUPS -----

import Cubical.Experiments.ZCohomology.Benchmarks

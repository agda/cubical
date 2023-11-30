{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Categories.Site.Instances.ZariskiCommRing where

-- TODO: clean up imports
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism
-- open import Cubical.Foundations.Powerset

open import Cubical.Data.Unit
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma
open import Cubical.Data.FinData

open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Localisation
open import Cubical.Algebra.CommRing.Ideal
open import Cubical.Algebra.CommRing.FGIdeal

open import Cubical.Categories.Category
open import Cubical.Categories.Instances.CommRings
open import Cubical.Categories.Site.Coverage
open import Cubical.Categories.Constructions.Slice

open import Cubical.HITs.PropositionalTruncation

open Category hiding (_∘_)
open isUnivalent
open isIso
open RingHoms
open IsRingHom

private
  variable
    ℓ ℓ' ℓ'' : Level

-- module _ (R' : CommRing ℓ) {n : ℕ} (f : FinVec (fst R') (suc n)) where
--  open isMultClosedSubset
--  open CommRingTheory R'
--  open RingTheory (CommRing→Ring R')
--  open Sum (CommRing→Ring R')
--  open CommIdeal R'
--  open InvertingElementsBase R'
--  open Exponentiation R'
--  open CommRingStr ⦃...⦄
--
--  private
--   R = fst R'
--   ⟨_⟩ : {n : ℕ} → FinVec R n → CommIdeal
--   ⟨ V ⟩ = ⟨ V ⟩[ R' ]
--   ⟨f₀,⋯,fₙ⟩ = ⟨ f ⟩[ R' ]

open Coverage

record UniModVec (R : CommRing ℓ) : Type ℓ where
  open CommRingStr (str R)
  open CommIdeal R using (_∈_)

  field
    n : ℕ
    f : FinVec ⟨ R ⟩ n
    isUniMod : 1r ∈ ⟨ f ⟩[ R ]

open SliceOb

zariskiCoverage : Coverage (CommRingsCategory {ℓ = ℓ} ^op) ℓ ℓ-zero
fst (covers zariskiCoverage R) = UniModVec R
fst (snd (covers zariskiCoverage R) um) = Fin n
  where
  open UniModVec um
S-ob (snd (snd (covers zariskiCoverage R) um) i) = R[1/ f i ]AsCommRing
  where
  open UniModVec um
  open InvertingElementsBase R
S-arr (snd (snd (covers zariskiCoverage R) um) i) = /1AsCommRingHom
  where
  open UniModVec um
  open InvertingElementsBase.UniversalProp R (f i)
pullbackStability zariskiCoverage {c = R} um {d = R'} φ =
  ∣ um' , (λ i → ∣ i , ψ i , RingHom≡ (sym (ψComm i)) ∣₁) ∣₁
  where
  open UniModVec
  um' : UniModVec R'
  um' .n = um .n
  um' .f i = φ $r um .f i
  um' .isUniMod = {!!}

  open InvertingElementsBase R
  open InvertingElementsBase R' renaming (R[1/_]AsCommRing to R'[1/_]AsCommRing) using ()
  ψ : (i : Fin (um .n)) → CommRingHom R[1/ um .f i ]AsCommRing R'[1/ um' .f i ]AsCommRing
  ψ i = uniqInvElemHom φ (um .f i) .fst .fst

  module R = UniversalProp
  module R' = InvertingElementsBase.UniversalProp R'
  ψComm : ∀ i → (ψ i .fst) ∘ (R._/1 (um .f i)) ≡ (R'._/1 (um' .f i)) ∘ φ .fst
  ψComm i = uniqInvElemHom φ (um .f i) .fst .snd

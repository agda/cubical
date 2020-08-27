-- This file needs to be rewritten so that Rng's are defined as a
-- record (as is the case for other algebraic structures like
-- rings). As this file isn't used for anything at the moment this
-- rewrite has been postponed.

{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Experiments.Rng where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.SIP
open import Cubical.Data.Sigma

open import Cubical.Structures.Axioms
open import Cubical.Structures.Auto
open import Cubical.Structures.Macro
open import Cubical.Algebra.Semigroup hiding (⟨_⟩)
open import Cubical.Algebra.AbGroup

private
  variable
    ℓ ℓ' : Level

module _ {ℓ} where
  rawRngDesc : Desc ℓ
  rawRngDesc = autoDesc (λ (X : Type ℓ) → (X → X → X) × (X → X → X))

  open Macro ℓ rawRngDesc public renaming
    ( structure to RawRngStructure
    ; equiv to RawRngEquivStr
    ; univalent to rawRngUnivalentStr
    )

RngAxioms : (X : Type ℓ) (s : RawRngStructure X) → Type ℓ
RngAxioms X (_·_ , _+_) =
  AbGroupΣTheory.AbGroupAxioms X _·_ ×
  SemigroupΣTheory.SemigroupAxioms X _+_ ×
  ((x y z : X) → x · (y + z) ≡ (x · y) + (x · z)) × ((x y z : X) → (x + y) · z ≡ (x · z) + (y · z))

RngStructure : Type ℓ → Type ℓ
RngStructure = AxiomsStructure RawRngStructure RngAxioms

Rng : Type (ℓ-suc ℓ)
Rng {ℓ} = TypeWithStr ℓ RngStructure

RngEquivStr : StrEquiv RngStructure ℓ
RngEquivStr = AxiomsEquivStr RawRngEquivStr RngAxioms

isPropRngAxioms : (X : Type ℓ) (s : RawRngStructure X) → isProp (RngAxioms X s)
isPropRngAxioms X (_·_ , _+_) = isPropΣ (AbGroupΣTheory.isPropAbGroupAxioms X _·_)
                                  λ _ → isPropΣ (SemigroupΣTheory.isPropSemigroupAxioms X _+_)
                                  λ { (isSetX , _) → isPropΣ (isPropΠ3 (λ _ _ _ → isSetX _ _))
                                  λ _ → isPropΠ3 (λ _ _ _ → isSetX _ _)}

rngUnivalentStr : UnivalentStr {ℓ} RngStructure RngEquivStr
rngUnivalentStr = axiomsUnivalentStr _ isPropRngAxioms rawRngUnivalentStr

RngPath : (M N : Rng {ℓ}) → (M ≃[ RngEquivStr ] N) ≃ (M ≡ N)
RngPath = SIP rngUnivalentStr

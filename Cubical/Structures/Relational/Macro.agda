{-

Descriptor language for easily defining relational structures

-}
{-# OPTIONS --cubical --no-import-sorts --no-exact-split --safe #-}
module Cubical.Structures.Relational.Macro where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.RelationalStructure

open import Cubical.Structures.Relational.Constant
open import Cubical.Structures.Relational.Join
open import Cubical.Structures.Relational.Maybe
open import Cubical.Structures.Relational.Parameterized
open import Cubical.Structures.Relational.Pointed
open import Cubical.Structures.Relational.UnaryOp

data RelDesc (ℓ : Level) : Typeω where
  -- constant structure: X ↦ A
  constant : ∀ {ℓ'} → hSet ℓ' → RelDesc ℓ
  -- pointed structure: X ↦ X
  var : RelDesc ℓ
  -- join of structures S,T : X ↦ (S X × T X)
  _,_ : RelDesc ℓ  → RelDesc ℓ  → RelDesc ℓ
  -- structure S parameterized by constant A : X ↦ (A → S X)
  param : ∀ {ℓ'} → (A : Type ℓ') → RelDesc ℓ  → RelDesc ℓ
  -- structure S parameterized by variable argument: X ↦ (X → S X)
  recvar : RelDesc ℓ  → RelDesc ℓ
  -- Maybe on a structure S: X ↦ Maybe (S X)
  maybe : RelDesc ℓ → RelDesc ℓ

infixr 4 _,_

{- Universe level calculations -}

relMacro-structure-level : ∀ {ℓ} → RelDesc ℓ → Level
relMacro-structure-level (constant {ℓ'} A) = ℓ'
relMacro-structure-level {ℓ} var = ℓ
relMacro-structure-level {ℓ} (d₀ , d₁) = ℓ-max (relMacro-structure-level d₀) (relMacro-structure-level d₁)
relMacro-structure-level (param {ℓ'} A d) = ℓ-max ℓ' (relMacro-structure-level d)
relMacro-structure-level {ℓ} (recvar d) = ℓ-max ℓ (relMacro-structure-level d)
relMacro-structure-level (maybe d) = relMacro-structure-level d

relMacro-rel-level : ∀ {ℓ} → RelDesc ℓ → Level
relMacro-rel-level (constant {ℓ'} x) = ℓ'
relMacro-rel-level {ℓ} var = ℓ
relMacro-rel-level {ℓ} (d₀ , d₁) = ℓ-max (relMacro-rel-level d₀) (relMacro-rel-level d₁)
relMacro-rel-level (param {ℓ'} A d) = ℓ-max ℓ' (relMacro-rel-level d)
relMacro-rel-level {ℓ} (recvar d) = ℓ-max ℓ (relMacro-rel-level d)
relMacro-rel-level (maybe d) = relMacro-rel-level d

-- Structure defined by a descriptor
relMacro-structure : ∀ {ℓ} → (d : RelDesc ℓ) → SetStructure ℓ (relMacro-structure-level d)
relMacro-structure (constant A) = constant-setStructure A
relMacro-structure var = pointed-setStructure
relMacro-structure (d₀ , d₁) = join-setStructure (relMacro-structure d₀) (relMacro-structure d₁)
relMacro-structure (param A d) = parameterized-setStructure A (λ _ → relMacro-structure d)
relMacro-structure (recvar d) = unaryFun-setStructure (relMacro-structure d)
relMacro-structure (maybe d) = maybe-setStructure (relMacro-structure d)

-- Notion of structured relmorphism defined by a descriptor
relMacro-rel : ∀ {ℓ} → (d : RelDesc ℓ) → StrRel {ℓ} (relMacro-structure d .struct) (relMacro-rel-level d)
relMacro-rel (constant A) = constant-propRel A
relMacro-rel var = pointed-propRel
relMacro-rel (d₀ , d₁) = join-propRel (relMacro-rel d₀) (relMacro-rel d₁)
relMacro-rel (param A d) = parameterized-propRel A (λ _ → relMacro-rel d)
relMacro-rel (recvar d) = unaryFun-propRel (relMacro-rel d)
relMacro-rel (maybe d) = maybe-propRel (relMacro-rel d)

-- Proof that structure induced by descriptor is a standard notion of structure
isSNRSRelMacro : ∀ {ℓ} → (d : RelDesc ℓ) → isSNRS (relMacro-structure d) (relMacro-rel d)
isSNRSRelMacro (constant A) = isSNRSConstant A
isSNRSRelMacro var = isSNRSPointed
isSNRSRelMacro (d₀ , d₁) = isSNRSJoin (isSNRSRelMacro d₀) (isSNRSRelMacro d₁)
isSNRSRelMacro (param A d) = isSNRSParameterized A (λ _ → isSNRSRelMacro d)
isSNRSRelMacro (recvar d) = isSNRSUnaryFun (isSNRSRelMacro d)
isSNRSRelMacro (maybe d) = isSNRSMaybe (isSNRSRelMacro d)


-- Module for easy importing
module RelMacro ℓ (d : RelDesc ℓ) where
  structure = relMacro-structure d
  relation = relMacro-rel d
  SNRS = isSNRSRelMacro d

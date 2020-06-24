{-

Descriptor language for easily defining relational structures

-}
{-# OPTIONS --cubical --no-import-sorts --no-exact-split --safe #-}
module Cubical.Structures.Relational.Macro where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.RelationalStructure

open import Cubical.Structures.Relational.Constant
open import Cubical.Structures.Relational.Product
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

RelMacroStrLevel : ∀ {ℓ} → RelDesc ℓ → Level
RelMacroStrLevel (constant {ℓ'} A) = ℓ'
RelMacroStrLevel {ℓ} var = ℓ
RelMacroStrLevel {ℓ} (d₀ , d₁) = ℓ-max (RelMacroStrLevel d₀) (RelMacroStrLevel d₁)
RelMacroStrLevel (param {ℓ'} A d) = ℓ-max ℓ' (RelMacroStrLevel d)
RelMacroStrLevel {ℓ} (recvar d) = ℓ-max ℓ (RelMacroStrLevel d)
RelMacroStrLevel (maybe d) = RelMacroStrLevel d

RelMacroRelLevel : ∀ {ℓ} → RelDesc ℓ → Level
RelMacroRelLevel (constant {ℓ'} x) = ℓ'
RelMacroRelLevel {ℓ} var = ℓ
RelMacroRelLevel {ℓ} (d₀ , d₁) = ℓ-max (RelMacroRelLevel d₀) (RelMacroRelLevel d₁)
RelMacroRelLevel (param {ℓ'} A d) = ℓ-max ℓ' (RelMacroRelLevel d)
RelMacroRelLevel {ℓ} (recvar d) = ℓ-max ℓ (RelMacroRelLevel d)
RelMacroRelLevel (maybe d) = RelMacroRelLevel d

-- Structure defined by a descriptor
RelMacroStructure : ∀ {ℓ} → (d : RelDesc ℓ) → SetStructure ℓ (RelMacroStrLevel d)
RelMacroStructure (constant A) = ConstantSetStructure A
RelMacroStructure var = PointedSetStructure
RelMacroStructure (d₀ , d₁) = ProductSetStructure (RelMacroStructure d₀) (RelMacroStructure d₁)
RelMacroStructure (param A d) = ParamSetStructure A (λ _ → RelMacroStructure d)
RelMacroStructure (recvar d) = UnaryFunSetStructure (RelMacroStructure d)
RelMacroStructure (maybe d) = MaybeSetStructure (RelMacroStructure d)

-- Notion of structured relmorphism defined by a descriptor
RelMacroRel : ∀ {ℓ} → (d : RelDesc ℓ) → StrRel {ℓ} (RelMacroStructure d .struct) (RelMacroRelLevel d)
RelMacroRel (constant A) = ConstantPropRel A
RelMacroRel var = PointedPropRel
RelMacroRel (d₀ , d₁) = ProductPropRel (RelMacroRel d₀) (RelMacroRel d₁)
RelMacroRel (param A d) = ParamPropRel A (λ _ → RelMacroRel d)
RelMacroRel (recvar d) = UnaryFunPropRel (RelMacroRel d)
RelMacroRel (maybe d) = MaybePropRel (RelMacroRel d)

-- Proof that structure induced by descriptor is a standard notion of structure
relMacroUnivalentRel : ∀ {ℓ} → (d : RelDesc ℓ) → isUnivalentRel (RelMacroStructure d) (RelMacroRel d)
relMacroUnivalentRel (constant A) = constantUnivalentRel A
relMacroUnivalentRel var = pointedUnivalentRel
relMacroUnivalentRel (d₀ , d₁) = productUnivalentRel (relMacroUnivalentRel d₀) (relMacroUnivalentRel d₁)
relMacroUnivalentRel (param A d) = paramUnivalentRel A (λ _ → relMacroUnivalentRel d)
relMacroUnivalentRel (recvar d) = unaryFunUnivalentRel (relMacroUnivalentRel d)
relMacroUnivalentRel (maybe d) = maybeUnivalentRel (relMacroUnivalentRel d)


-- Module for easy importing
module RelMacro ℓ (d : RelDesc ℓ) where
  structure = RelMacroStructure d
  relation = RelMacroRel d
  univalent = relMacroUnivalentRel d

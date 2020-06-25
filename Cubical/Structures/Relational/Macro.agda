{-

Descriptor language for easily defining relational structures

-}
{-# OPTIONS --cubical --no-import-sorts --no-exact-split --safe #-}
module Cubical.Structures.Relational.Macro where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.RelationalStructure

open import Cubical.Structures.Relational.Constant
open import Cubical.Structures.Relational.Product
open import Cubical.Structures.Relational.Maybe
open import Cubical.Structures.Relational.Parameterized
open import Cubical.Structures.Relational.Pointed
open import Cubical.Structures.Relational.UnaryOp

open import Cubical.Structures.Macro

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

relDesc→Desc : ∀ {ℓ} → RelDesc ℓ → Desc ℓ
relDesc→Desc (constant A) = constant (A .fst)
relDesc→Desc var = var
relDesc→Desc (d₀ , d₁) = relDesc→Desc d₀ , relDesc→Desc d₁
relDesc→Desc (param A d) = param A (relDesc→Desc d)
relDesc→Desc (recvar d) = recvar (relDesc→Desc d)
relDesc→Desc (maybe d) = maybe (relDesc→Desc d)

relMacroStrLevel : ∀ {ℓ} → RelDesc ℓ → Level
relMacroStrLevel d = macroStrLevel (relDesc→Desc d)

relMacroRelLevel : ∀ {ℓ} → RelDesc ℓ → Level
relMacroRelLevel d = macroEquivLevel (relDesc→Desc d)

RelMacroStructure : ∀ {ℓ} → (d : RelDesc ℓ) → Type ℓ → Type (relMacroStrLevel d)
RelMacroStructure d = MacroStructure (relDesc→Desc d)

preservesSetsRelMacro : ∀ {ℓ} → (d : RelDesc ℓ)
  {X : Type ℓ} → isSet X → isSet (RelMacroStructure d X)
preservesSetsRelMacro (constant A) = preservesSetsConstant A
preservesSetsRelMacro var = preservesSetsPointed
preservesSetsRelMacro (d₀ , d₁) =
  preservesSetsProduct (preservesSetsRelMacro d₀) (preservesSetsRelMacro d₁)
preservesSetsRelMacro (param A d) =
  preservesSetsParam A (λ _ → preservesSetsRelMacro d)
preservesSetsRelMacro (recvar d) =
  preservesSetsUnaryFun (preservesSetsRelMacro d)
preservesSetsRelMacro (maybe d) =
  preservesSetsMaybe (preservesSetsRelMacro d)

-- Notion of structured relation defined by a descriptor
RelMacroRelStr : ∀ {ℓ} → (d : RelDesc ℓ) → StrRel {ℓ} (RelMacroStructure d) (relMacroRelLevel d)
RelMacroRelStr (constant A) = ConstantRelStr A
RelMacroRelStr var = PointedRelStr
RelMacroRelStr (d₀ , d₁) = ProductRelStr (RelMacroRelStr d₀) (RelMacroRelStr d₁)
RelMacroRelStr (param A d) = ParamRelStr A (λ _ → RelMacroRelStr d)
RelMacroRelStr (recvar d) = UnaryFunRelStr (RelMacroRelStr d)
RelMacroRelStr (maybe d) = MaybeRelStr (RelMacroRelStr d)

-- Proof that structure induced by descriptor is suitable
relMacroSuitableRel : ∀ {ℓ} → (d : RelDesc ℓ) → SuitableStrRel _ (RelMacroRelStr d)
relMacroSuitableRel (constant A) = constantSuitableRel A
relMacroSuitableRel var = pointedSuitableRel
relMacroSuitableRel (d₀ , d₁) = productSuitableRel (relMacroSuitableRel d₀) (relMacroSuitableRel d₁)
relMacroSuitableRel (param A d) = paramSuitableRel A (λ _ → relMacroSuitableRel d)
relMacroSuitableRel (recvar d) = unaryFunSuitableRel (preservesSetsRelMacro d) (relMacroSuitableRel d)
relMacroSuitableRel (maybe d) = maybeSuitableRel (relMacroSuitableRel d)

-- Proof that structured relations and equivalences agree
relMacroMatchesEquiv : ∀ {ℓ} → (d : RelDesc ℓ)
  → StrRelMatchesEquiv (RelMacroRelStr d) (MacroEquivStr (relDesc→Desc d))
relMacroMatchesEquiv (constant A) = constantRelMatchesEquiv A
relMacroMatchesEquiv var = pointedRelMatchesEquiv
relMacroMatchesEquiv (d₁ , d₂) =
  productRelMatchesEquiv
    (RelMacroRelStr d₁) (RelMacroRelStr d₂)
    (relMacroMatchesEquiv d₁) (relMacroMatchesEquiv d₂)
relMacroMatchesEquiv (param A d) =
  paramRelMatchesEquiv A (λ _ → RelMacroRelStr d) (λ _ → relMacroMatchesEquiv d)
relMacroMatchesEquiv (recvar d) =
  unaryFunRelMatchesEquiv (RelMacroRelStr d) (relMacroMatchesEquiv d)
relMacroMatchesEquiv (maybe d) =
  maybeRelMatchesEquiv (RelMacroRelStr d) (relMacroMatchesEquiv d)

-- Module for easy importing
module RelMacro ℓ (d : RelDesc ℓ) where
  relation = RelMacroRelStr d
  suitable = relMacroSuitableRel d
  matches = relMacroMatchesEquiv d
  open Macro ℓ (relDesc→Desc d) public

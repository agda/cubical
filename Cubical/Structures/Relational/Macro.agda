{-

Descriptor language for easily defining relational structures

-}
{-# OPTIONS --cubical --no-import-sorts --no-exact-split --safe #-}
module Cubical.Structures.Relational.Macro where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.RelationalStructure
open import Cubical.Data.Sigma

open import Cubical.Structures.Relational.Constant
open import Cubical.Structures.Relational.Function
open import Cubical.Structures.Relational.Maybe
open import Cubical.Structures.Relational.Parameterized
open import Cubical.Structures.Relational.Pointed
open import Cubical.Structures.Relational.Product

open import Cubical.Structures.Macro
open import Cubical.Structures.Maybe

data PosRelDesc (ℓ : Level) : Typeω where
  -- constant structure: X ↦ A
  constant : ∀ {ℓ'} → hSet ℓ' → PosRelDesc ℓ
  -- pointed structure: X ↦ X
  var : PosRelDesc ℓ
  -- product of structures S,T : X ↦ (S X × T X)
  _,_ : PosRelDesc ℓ  → PosRelDesc ℓ  → PosRelDesc ℓ
  -- Maybe on a structure S: X ↦ Maybe (S X)
  maybe : PosRelDesc ℓ → PosRelDesc ℓ

data RelDesc (ℓ : Level) : Typeω where
  -- constant structure: X ↦ A
  constant : ∀ {ℓ'} → hSet ℓ' → RelDesc ℓ
  -- pointed structure: X ↦ X
  var : RelDesc ℓ
  -- product of structures S,T : X ↦ (S X × T X)
  _,_ : RelDesc ℓ  → RelDesc ℓ  → RelDesc ℓ
  -- structure S parameterized by constant A : X ↦ (A → S X)
  param : ∀ {ℓ'} → (A : Type ℓ') → RelDesc ℓ  → RelDesc ℓ
  -- function from positive structure S to T: X ↦ (S X → T X)
  function+ : PosRelDesc ℓ → RelDesc ℓ → RelDesc ℓ
  -- Maybe on a structure S: X ↦ Maybe (S X)
  maybe : RelDesc ℓ → RelDesc ℓ

infixr 4 _,_

posRelDesc→TranspDesc : ∀ {ℓ} → PosRelDesc ℓ → TranspDesc ℓ
posRelDesc→TranspDesc (constant A) = constant (A .fst)
posRelDesc→TranspDesc var = var
posRelDesc→TranspDesc (d₀ , d₁) = posRelDesc→TranspDesc d₀ , posRelDesc→TranspDesc d₁
posRelDesc→TranspDesc (maybe d) = maybe (posRelDesc→TranspDesc d)

posRelDesc→RelDesc : ∀ {ℓ} → PosRelDesc ℓ → RelDesc ℓ
posRelDesc→RelDesc (constant A) = constant A
posRelDesc→RelDesc var = var
posRelDesc→RelDesc (d₀ , d₁) = posRelDesc→RelDesc d₀ , posRelDesc→RelDesc d₁
posRelDesc→RelDesc (maybe d) = maybe (posRelDesc→RelDesc d)

relDesc→Desc : ∀ {ℓ} → RelDesc ℓ → Desc ℓ
relDesc→Desc (constant A) = constant (A .fst)
relDesc→Desc var = var
relDesc→Desc (d₀ , d₁) = relDesc→Desc d₀ , relDesc→Desc d₁
relDesc→Desc (param A d) = function+ (constant A) (relDesc→Desc d)
relDesc→Desc (function+ d₀ d₁) = function+ (posRelDesc→TranspDesc d₀) (relDesc→Desc d₁)
relDesc→Desc (maybe d) = maybe (relDesc→Desc d)

{- Universe level calculations -}

posRelMacroStrLevel : ∀ {ℓ} → PosRelDesc ℓ → Level
posRelMacroStrLevel d = transpMacroLevel (posRelDesc→TranspDesc d)

relMacroStrLevel : ∀ {ℓ} → RelDesc ℓ → Level
relMacroStrLevel d = macroStrLevel (relDesc→Desc d)

posRelMacroRelLevel : ∀ {ℓ} → PosRelDesc ℓ → Level
posRelMacroRelLevel (constant {ℓ'} A) = ℓ'
posRelMacroRelLevel {ℓ} var = ℓ
posRelMacroRelLevel (d₀ , d₁) = ℓ-max (posRelMacroRelLevel d₀) (posRelMacroRelLevel d₁)
posRelMacroRelLevel (maybe d) = posRelMacroRelLevel d

relMacroRelLevel : ∀ {ℓ} → RelDesc ℓ → Level
relMacroRelLevel (constant {ℓ'} A) = ℓ'
relMacroRelLevel {ℓ} var = ℓ
relMacroRelLevel (d₀ , d₁) = ℓ-max (relMacroRelLevel d₀) (relMacroRelLevel d₁)
relMacroRelLevel (param {ℓ'} A d) = ℓ-max ℓ' (relMacroRelLevel d)
relMacroRelLevel (function+ d₀ d₁) =
  ℓ-max (posRelMacroStrLevel d₀) (ℓ-max (posRelMacroRelLevel d₀) (relMacroRelLevel d₁))
relMacroRelLevel (maybe d) = relMacroRelLevel d

{- Definition of structure -}

PosRelMacroStructure : ∀ {ℓ} (d : PosRelDesc ℓ) → Type ℓ → Type (posRelMacroStrLevel d)
PosRelMacroStructure d = TranspMacroStructure (posRelDesc→TranspDesc d)

RelMacroStructure : ∀ {ℓ} (d : RelDesc ℓ) → Type ℓ → Type (relMacroStrLevel d)
RelMacroStructure d = MacroStructure (relDesc→Desc d)

{- Notion of structured relation defined by a descriptor -}

PosRelMacroRelStr : ∀ {ℓ} (d : PosRelDesc ℓ) → StrRel {ℓ} (PosRelMacroStructure d) (posRelMacroRelLevel d)
PosRelMacroRelStr (constant A) = ConstantRelStr A
PosRelMacroRelStr var = PointedRelStr
PosRelMacroRelStr (d₀ , d₁) = ProductRelStr (PosRelMacroRelStr d₀) (PosRelMacroRelStr d₁)
PosRelMacroRelStr (maybe d) = MaybeRelStr (PosRelMacroRelStr d)

RelMacroRelStr : ∀ {ℓ} (d : RelDesc ℓ) → StrRel {ℓ} (RelMacroStructure d) (relMacroRelLevel d)
RelMacroRelStr (constant A) = ConstantRelStr A
RelMacroRelStr var = PointedRelStr
RelMacroRelStr (d₀ , d₁) = ProductRelStr (RelMacroRelStr d₀) (RelMacroRelStr d₁)
RelMacroRelStr (param A d) = ParamRelStr A (λ _ → RelMacroRelStr d)
RelMacroRelStr (function+ d₀ d₁) =
  FunctionRelStr (PosRelMacroRelStr d₀)  (RelMacroRelStr d₁)
RelMacroRelStr (maybe d) = MaybeRelStr (RelMacroRelStr d)

{- Proof that structure induced by descriptor is suitable or positive -}

posRelMacroSuitableRel : ∀ {ℓ} (d : PosRelDesc ℓ) → SuitableStrRel _ (PosRelMacroRelStr d)
posRelMacroSuitableRel (constant A) = constantSuitableRel A
posRelMacroSuitableRel var = pointedSuitableRel
posRelMacroSuitableRel (d₀ , d₁) =
  productSuitableRel (posRelMacroSuitableRel d₀) (posRelMacroSuitableRel d₁)
posRelMacroSuitableRel (maybe d) = maybeSuitableRel (posRelMacroSuitableRel d)

posRelMacroPositiveRel : ∀ {ℓ} (d : PosRelDesc ℓ) → PositiveStrRel (posRelMacroSuitableRel d)
posRelMacroPositiveRel (constant A) = constantPositiveRel A
posRelMacroPositiveRel var = pointedPositiveRel
posRelMacroPositiveRel (d₀ , d₁) =
  productPositiveRel (posRelMacroPositiveRel d₀) (posRelMacroPositiveRel d₁)
posRelMacroPositiveRel (maybe d) = maybePositiveRel (posRelMacroPositiveRel d)

relMacroSuitableRel : ∀ {ℓ} (d : RelDesc ℓ) → SuitableStrRel _ (RelMacroRelStr d)
relMacroSuitableRel (constant A) = constantSuitableRel A
relMacroSuitableRel var = pointedSuitableRel
relMacroSuitableRel (d₀ , d₁) = productSuitableRel (relMacroSuitableRel d₀) (relMacroSuitableRel d₁)
relMacroSuitableRel (param A d) = paramSuitableRel A (λ _ → relMacroSuitableRel d)
relMacroSuitableRel (function+ d₀ d₁) =
  functionSuitableRel (posRelMacroSuitableRel d₀) (posRelMacroPositiveRel d₀) (relMacroSuitableRel d₁)
relMacroSuitableRel (maybe d) = maybeSuitableRel (relMacroSuitableRel d)

{- Proof that structured relations and equivalences agree -}

posRelMacroMatchesEquiv : ∀ {ℓ} (d : PosRelDesc ℓ)
  → StrRelMatchesEquiv (PosRelMacroRelStr d) (EquivAction→StrEquiv (transpMacroAction (posRelDesc→TranspDesc d)))
posRelMacroMatchesEquiv (constant A) _ _ _ = idEquiv _
posRelMacroMatchesEquiv var _ _ _ = idEquiv _
posRelMacroMatchesEquiv (d₀ , d₁) =
  productRelMatchesTransp
    (PosRelMacroRelStr d₀) (transpMacroAction (posRelDesc→TranspDesc d₀))
    (PosRelMacroRelStr d₁) (transpMacroAction (posRelDesc→TranspDesc d₁))
    (posRelMacroMatchesEquiv d₀) (posRelMacroMatchesEquiv d₁)
posRelMacroMatchesEquiv (maybe d) =
  maybeRelMatchesTransp
    (PosRelMacroRelStr d) (transpMacroAction (posRelDesc→TranspDesc d))
    (posRelMacroMatchesEquiv d)

relMacroMatchesEquiv : ∀ {ℓ} (d : RelDesc ℓ)
  → StrRelMatchesEquiv (RelMacroRelStr d) (MacroEquivStr (relDesc→Desc d))
relMacroMatchesEquiv (constant A) = constantRelMatchesEquiv A
relMacroMatchesEquiv var = pointedRelMatchesEquiv
relMacroMatchesEquiv (d₁ , d₂) =
  productRelMatchesEquiv
    (RelMacroRelStr d₁) (RelMacroRelStr d₂)
    (relMacroMatchesEquiv d₁) (relMacroMatchesEquiv d₂)
relMacroMatchesEquiv (param A d) =
  paramRelMatchesEquiv A (λ _ → RelMacroRelStr d) (λ _ → relMacroMatchesEquiv d)
relMacroMatchesEquiv (function+ d₀ d₁) =
  functionRelMatchesEquiv+
    (PosRelMacroRelStr d₀) (transpMacroAction (posRelDesc→TranspDesc d₀))
    (RelMacroRelStr d₁) (MacroEquivStr (relDesc→Desc d₁))
    (posRelMacroMatchesEquiv d₀) (relMacroMatchesEquiv d₁)
relMacroMatchesEquiv (maybe d) =
  maybeRelMatchesEquiv (RelMacroRelStr d) (relMacroMatchesEquiv d)

-- Module for easy importing
module RelMacro ℓ (d : RelDesc ℓ) where
  relation = RelMacroRelStr d
  suitable = relMacroSuitableRel d
  matches = relMacroMatchesEquiv d
  open Macro ℓ (relDesc→Desc d) public

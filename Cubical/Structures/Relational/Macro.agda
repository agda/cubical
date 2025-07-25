{-

Descriptor language for easily defining relational structures

-}
{-# OPTIONS --no-exact-split #-}
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

data PosRelDesc (ℓ : Level) : Level → Typeω where
  -- constant structure: X ↦ A
  constant : ∀ {ℓ₁} → hSet ℓ₁ → PosRelDesc ℓ ℓ₁
  -- pointed structure: X ↦ X
  var : PosRelDesc ℓ ℓ
  -- product of structures S,T : X ↦ (S X × T X)
  _,_ : ∀ {ℓ₁ ℓ₂} → PosRelDesc ℓ ℓ₁ → PosRelDesc ℓ ℓ₂ → PosRelDesc ℓ (ℓ-max ℓ₁ ℓ₂)
  -- Maybe on a structure S: X ↦ Maybe (S X)
  maybe : ∀ {ℓ₁} → PosRelDesc ℓ ℓ₁ → PosRelDesc ℓ ℓ₁

data RelDesc (ℓ : Level) : Level → Level → Typeω where
  -- constant structure: X ↦ A
  constant : ∀ {ℓ₁} → hSet ℓ₁ → RelDesc ℓ ℓ₁ ℓ₁
  -- pointed structure: X ↦ X
  var : RelDesc ℓ ℓ ℓ
  -- product of structures S,T : X ↦ (S X × T X)
  _,_ : ∀ {ℓ₁ ℓ₁' ℓ₂ ℓ₂'} → RelDesc ℓ ℓ₁ ℓ₁' → RelDesc ℓ ℓ₂ ℓ₂' → RelDesc ℓ (ℓ-max ℓ₁ ℓ₂) (ℓ-max ℓ₁' ℓ₂')
  -- structure S parameterized by constant A : X ↦ (A → S X)
  param : ∀ {ℓ₁ ℓ₂ ℓ₂'} → (A : Type ℓ₁) → RelDesc ℓ ℓ₂ ℓ₂' → RelDesc ℓ (ℓ-max ℓ₁ ℓ₂) (ℓ-max ℓ₁ ℓ₂')
  -- function from positive structure S to T: X ↦ (S X → T X)
  function+ : ∀ {ℓ₁ ℓ₂ ℓ₂'} → PosRelDesc ℓ ℓ₁ → RelDesc ℓ ℓ₂ ℓ₂' → RelDesc ℓ (ℓ-max ℓ₁ ℓ₂) (ℓ-max ℓ₁ ℓ₂')
  -- Maybe on a structure S: X ↦ Maybe (S X)
  maybe : ∀ {ℓ₁ ℓ₁'} → RelDesc ℓ ℓ₁ ℓ₁' → RelDesc ℓ ℓ₁ ℓ₁'

infixr 4 _,_

posRelDesc→TranspDesc : ∀ {ℓ ℓ₁} → PosRelDesc ℓ ℓ₁ → TranspDesc ℓ ℓ₁
posRelDesc→TranspDesc (constant A) = constant (A .fst)
posRelDesc→TranspDesc var = var
posRelDesc→TranspDesc (d₀ , d₁) = posRelDesc→TranspDesc d₀ , posRelDesc→TranspDesc d₁
posRelDesc→TranspDesc (maybe d) = maybe (posRelDesc→TranspDesc d)

posRelDesc→RelDesc : ∀ {ℓ ℓ₁} → PosRelDesc ℓ ℓ₁ → RelDesc ℓ ℓ₁ ℓ₁
posRelDesc→RelDesc (constant A) = constant A
posRelDesc→RelDesc var = var
posRelDesc→RelDesc (d₀ , d₁) = posRelDesc→RelDesc d₀ , posRelDesc→RelDesc d₁
posRelDesc→RelDesc (maybe d) = maybe (posRelDesc→RelDesc d)

relDesc→Desc : ∀ {ℓ ℓ₁ ℓ₁'} → RelDesc ℓ ℓ₁ ℓ₁' → Desc ℓ ℓ₁ ℓ₁'
relDesc→Desc (constant A) = constant (A .fst)
relDesc→Desc var = var
relDesc→Desc (d₀ , d₁) = relDesc→Desc d₀ , relDesc→Desc d₁
relDesc→Desc (param A d) = function+ (constant A) (relDesc→Desc d)
relDesc→Desc (function+ d₀ d₁) = function+ (posRelDesc→TranspDesc d₀) (relDesc→Desc d₁)
relDesc→Desc (maybe d) = maybe (relDesc→Desc d)

{- Definition of structure -}

PosRelMacroStructure : ∀ {ℓ ℓ₁} (d : PosRelDesc ℓ ℓ₁) → Type ℓ → Type ℓ₁
PosRelMacroStructure d = TranspMacroStructure (posRelDesc→TranspDesc d)

RelMacroStructure : ∀ {ℓ ℓ₁ ℓ₁'} (d : RelDesc ℓ ℓ₁ ℓ₁') → Type ℓ → Type ℓ₁
RelMacroStructure d = MacroStructure (relDesc→Desc d)

{- Notion of structured relation defined by a descriptor -}

PosRelMacroRelStr : ∀ {ℓ ℓ₁} (d : PosRelDesc ℓ ℓ₁) → StrRel (PosRelMacroStructure d) ℓ₁
PosRelMacroRelStr (constant A) = ConstantRelStr A
PosRelMacroRelStr var = PointedRelStr
PosRelMacroRelStr (d₀ , d₁) = ProductRelStr (PosRelMacroRelStr d₀) (PosRelMacroRelStr d₁)
PosRelMacroRelStr (maybe d) = MaybeRelStr (PosRelMacroRelStr d)

RelMacroRelStr : ∀ {ℓ ℓ₁ ℓ₁'} (d : RelDesc ℓ ℓ₁ ℓ₁') → StrRel (RelMacroStructure d) ℓ₁'
RelMacroRelStr (constant A) = ConstantRelStr A
RelMacroRelStr var = PointedRelStr
RelMacroRelStr (d₀ , d₁) = ProductRelStr (RelMacroRelStr d₀) (RelMacroRelStr d₁)
RelMacroRelStr (param A d) = ParamRelStr A (λ _ → RelMacroRelStr d)
RelMacroRelStr (function+ d₀ d₁) =
  FunctionRelStr (PosRelMacroRelStr d₀)  (RelMacroRelStr d₁)
RelMacroRelStr (maybe d) = MaybeRelStr (RelMacroRelStr d)

{- Proof that structure induced by descriptor is suitable or positive -}

posRelMacroSuitableRel : ∀ {ℓ ℓ₁} (d : PosRelDesc ℓ ℓ₁) → SuitableStrRel _ (PosRelMacroRelStr d)
posRelMacroSuitableRel (constant A) = constantSuitableRel A
posRelMacroSuitableRel var = pointedSuitableRel
posRelMacroSuitableRel (d₀ , d₁) =
  productSuitableRel (posRelMacroSuitableRel d₀) (posRelMacroSuitableRel d₁)
posRelMacroSuitableRel (maybe d) = maybeSuitableRel (posRelMacroSuitableRel d)

posRelMacroPositiveRel : ∀ {ℓ ℓ₁} (d : PosRelDesc ℓ ℓ₁) → PositiveStrRel (posRelMacroSuitableRel d)
posRelMacroPositiveRel (constant A) = constantPositiveRel A
posRelMacroPositiveRel var = pointedPositiveRel
posRelMacroPositiveRel (d₀ , d₁) =
  productPositiveRel (posRelMacroPositiveRel d₀) (posRelMacroPositiveRel d₁)
posRelMacroPositiveRel (maybe d) = maybePositiveRel (posRelMacroPositiveRel d)

relMacroSuitableRel : ∀ {ℓ ℓ₁ ℓ₁'} (d : RelDesc ℓ ℓ₁ ℓ₁') → SuitableStrRel _ (RelMacroRelStr d)
relMacroSuitableRel (constant A) = constantSuitableRel A
relMacroSuitableRel var = pointedSuitableRel
relMacroSuitableRel (d₀ , d₁) = productSuitableRel (relMacroSuitableRel d₀) (relMacroSuitableRel d₁)
relMacroSuitableRel (param A d) = paramSuitableRel A (λ _ → relMacroSuitableRel d)
relMacroSuitableRel (function+ d₀ d₁) =
  functionSuitableRel (posRelMacroSuitableRel d₀) (posRelMacroPositiveRel d₀) (relMacroSuitableRel d₁)
relMacroSuitableRel (maybe d) = maybeSuitableRel (relMacroSuitableRel d)

{- Proof that structured relations and equivalences agree -}

posRelMacroMatchesEquiv : ∀ {ℓ ℓ₁} (d : PosRelDesc ℓ ℓ₁)
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

relMacroMatchesEquiv : ∀ {ℓ ℓ₁ ℓ₁'} (d : RelDesc ℓ ℓ₁ ℓ₁')
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
module RelMacro ℓ {ℓ₁ ℓ₁'} (d : RelDesc ℓ ℓ₁ ℓ₁') where
  relation = RelMacroRelStr d
  suitable = relMacroSuitableRel d
  matches = relMacroMatchesEquiv d
  open Macro ℓ (relDesc→Desc d) public

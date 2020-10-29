{-

Descriptor language for easily defining structures

-}
{-# OPTIONS --cubical --no-import-sorts --no-exact-split --safe #-}
module Cubical.Structures.Macro where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.SIP
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe

open import Cubical.Structures.Constant
open import Cubical.Structures.Function
open import Cubical.Structures.Maybe
open import Cubical.Structures.Parameterized
open import Cubical.Structures.Pointed
open import Cubical.Structures.Product

data TranspDesc (ℓ : Level) : Typeω where
  -- constant structure: X ↦ A
  constant : ∀ {ℓ'} (A : Type ℓ') → TranspDesc ℓ
  -- pointed structure: X ↦ X
  var : TranspDesc ℓ
  -- product of structures S,T : X ↦ (S X × T X)
  _,_ : (d₀ : TranspDesc ℓ) (d₁ : TranspDesc ℓ) → TranspDesc ℓ
  -- functions between structures S,T: X ↦ (S X → T X)
  function : (d₀ : TranspDesc ℓ) (d₁ : TranspDesc ℓ) → TranspDesc ℓ
  -- Maybe on a structure S: X ↦ Maybe (S X)
  maybe : TranspDesc ℓ → TranspDesc ℓ
  -- arbitrary transport structure
  foreign : ∀ {ℓ'} {S : Type ℓ → Type ℓ'} (α : EquivAction S) → TransportStr α → TranspDesc ℓ

data Desc (ℓ : Level) : Typeω where
  -- constant structure: X ↦ A
  constant : ∀ {ℓ'} (A : Type ℓ') → Desc ℓ
  -- pointed structure: X ↦ X
  var : Desc ℓ
  -- product of structures S,T : X ↦ (S X × T X)
  _,_ : (d₀ : Desc ℓ) (d₁ : Desc ℓ) → Desc ℓ
  -- functions between structures S,T : X ↦ (S X → T X)
  function : (d₀ : Desc ℓ) (d₁ : Desc ℓ) → Desc ℓ
  -- functions between structures S,T where S is functorial : X ↦ (S X → T X)
  function+ : (d₀ : TranspDesc ℓ) (d₁ : Desc ℓ) → Desc ℓ
  -- Maybe on a structure S: X ↦ Maybe (S X)
  maybe : Desc ℓ → Desc ℓ
  -- univalent structure from transport structure
  transpDesc : TranspDesc ℓ → Desc ℓ
  -- arbitrary univalent notion of structure
  foreign : ∀ {ℓ' ℓ''} {S : Type ℓ → Type ℓ'} (ι : StrEquiv S ℓ'') → UnivalentStr S ι → Desc ℓ

infixr 4 _,_

{- Transport structures -}

transpMacroLevel : ∀ {ℓ} → TranspDesc ℓ → Level
transpMacroLevel (constant {ℓ'} x) = ℓ'
transpMacroLevel {ℓ} var = ℓ
transpMacroLevel {ℓ} (d₀ , d₁) = ℓ-max (transpMacroLevel d₀) (transpMacroLevel d₁)
transpMacroLevel (function d₀ d₁) = ℓ-max (transpMacroLevel d₀) (transpMacroLevel d₁)
transpMacroLevel (maybe d) = transpMacroLevel d
transpMacroLevel (foreign {ℓ'} α τ) = ℓ'

-- Structure defined by a transport descriptor
TranspMacroStructure : ∀ {ℓ} (d : TranspDesc ℓ) → Type ℓ → Type (transpMacroLevel d)
TranspMacroStructure (constant A) X = A
TranspMacroStructure var X = X
TranspMacroStructure (d₀ , d₁) X = TranspMacroStructure d₀ X × TranspMacroStructure d₁ X
TranspMacroStructure (function d₀ d₁) X = TranspMacroStructure d₀ X → TranspMacroStructure d₁ X
TranspMacroStructure (maybe d) = MaybeStructure (TranspMacroStructure d)
TranspMacroStructure (foreign {S = S} α τ) = S

-- Action defined by a transport descriptor
transpMacroAction : ∀ {ℓ} (d : TranspDesc ℓ) → EquivAction (TranspMacroStructure d)
transpMacroAction (constant A) = constantEquivAction A
transpMacroAction var = pointedEquivAction
transpMacroAction (d₀ , d₁) = productEquivAction (transpMacroAction d₀) (transpMacroAction d₁)
transpMacroAction (function d₀ d₁) =
  functionEquivAction (transpMacroAction d₀) (transpMacroAction d₁)
transpMacroAction (maybe d) = maybeEquivAction (transpMacroAction d)
transpMacroAction (foreign α _) = α

-- Action defines a transport structure
transpMacroTransportStr : ∀ {ℓ} (d : TranspDesc ℓ) → TransportStr (transpMacroAction d)
transpMacroTransportStr (constant A) = constantTransportStr A
transpMacroTransportStr var = pointedTransportStr
transpMacroTransportStr (d₀ , d₁) =
  productTransportStr
    (transpMacroAction d₀) (transpMacroTransportStr d₀)
    (transpMacroAction d₁) (transpMacroTransportStr d₁)
transpMacroTransportStr (function d₀ d₁) =
  functionTransportStr
    (transpMacroAction d₀) (transpMacroTransportStr d₀)
    (transpMacroAction d₁) (transpMacroTransportStr d₁)
transpMacroTransportStr (maybe d) =
  maybeTransportStr (transpMacroAction d) (transpMacroTransportStr d)
transpMacroTransportStr (foreign α τ) = τ

{- General structures -}

macroStrLevel : ∀ {ℓ} → Desc ℓ → Level
macroStrLevel (constant {ℓ'} x) = ℓ'
macroStrLevel {ℓ} var = ℓ
macroStrLevel {ℓ} (d₀ , d₁) = ℓ-max (macroStrLevel d₀) (macroStrLevel d₁)
macroStrLevel {ℓ} (function+ d₀ d₁) = ℓ-max (transpMacroLevel d₀) (macroStrLevel d₁)
macroStrLevel (function d₀ d₁) = ℓ-max (macroStrLevel d₀) (macroStrLevel d₁)
macroStrLevel (maybe d) = macroStrLevel d
macroStrLevel (transpDesc d) = transpMacroLevel d
macroStrLevel (foreign {ℓ'} _ _) = ℓ'

macroEquivLevel : ∀ {ℓ} → Desc ℓ → Level
macroEquivLevel (constant {ℓ'} x) = ℓ'
macroEquivLevel {ℓ} var = ℓ
macroEquivLevel (d₀ , d₁) = ℓ-max (macroEquivLevel d₀) (macroEquivLevel d₁)
macroEquivLevel {ℓ} (function+ d₀ d₁) = ℓ-max (transpMacroLevel d₀) (macroEquivLevel d₁)
macroEquivLevel (function d₀ d₁) = ℓ-max (macroStrLevel d₀) (ℓ-max (macroEquivLevel d₀) (macroEquivLevel d₁))
macroEquivLevel (maybe d) = macroEquivLevel d
macroEquivLevel (transpDesc d) = transpMacroLevel d
macroEquivLevel (foreign {ℓ'' = ℓ''} _ _) = ℓ''

-- Structure defined by a descriptor
MacroStructure : ∀ {ℓ} (d : Desc ℓ) → Type ℓ → Type (macroStrLevel d)
MacroStructure (constant A) X = A
MacroStructure var X = X
MacroStructure (d₀ , d₁) X = MacroStructure d₀ X × MacroStructure d₁ X
MacroStructure (function+ d₀ d₁) X = TranspMacroStructure d₀ X → MacroStructure d₁ X
MacroStructure (function d₀ d₁) X = MacroStructure d₀ X → MacroStructure d₁ X
MacroStructure (maybe d) = MaybeStructure (MacroStructure d)
MacroStructure (transpDesc d) = TranspMacroStructure d
MacroStructure (foreign {S = S} _ _) = S

-- Notion of structured equivalence defined by a descriptor
MacroEquivStr : ∀ {ℓ} → (d : Desc ℓ) → StrEquiv {ℓ} (MacroStructure d) (macroEquivLevel d)
MacroEquivStr (constant A) = ConstantEquivStr A
MacroEquivStr var = PointedEquivStr
MacroEquivStr (d₀ , d₁) = ProductEquivStr (MacroEquivStr d₀) (MacroEquivStr d₁)
MacroEquivStr (function+ d₀ d₁) = FunctionEquivStr+ (transpMacroAction d₀) (MacroEquivStr d₁)
MacroEquivStr (function d₀ d₁) = FunctionEquivStr (MacroEquivStr d₀) (MacroEquivStr d₁)
MacroEquivStr (maybe d) = MaybeEquivStr (MacroEquivStr d)
MacroEquivStr (transpDesc d) = EquivAction→StrEquiv (transpMacroAction d)
MacroEquivStr (foreign ι _) = ι

-- Proof that structure induced by descriptor is univalent
MacroUnivalentStr : ∀ {ℓ} → (d : Desc ℓ) → UnivalentStr (MacroStructure d) (MacroEquivStr d)
MacroUnivalentStr (constant A) = constantUnivalentStr A
MacroUnivalentStr var = pointedUnivalentStr
MacroUnivalentStr (d₀ , d₁) =
  productUnivalentStr
    (MacroEquivStr d₀) (MacroUnivalentStr d₀)
    (MacroEquivStr d₁) (MacroUnivalentStr d₁)
MacroUnivalentStr (function+ d₀ d₁) =
  functionUnivalentStr+
    (transpMacroAction d₀) (transpMacroTransportStr d₀)
    (MacroEquivStr d₁) (MacroUnivalentStr d₁)
MacroUnivalentStr (function d₀ d₁) =
  functionUnivalentStr
    (MacroEquivStr d₀) (MacroUnivalentStr d₀)
    (MacroEquivStr d₁) (MacroUnivalentStr d₁)
MacroUnivalentStr (maybe d) = maybeUnivalentStr (MacroEquivStr d) (MacroUnivalentStr d)
MacroUnivalentStr (transpDesc d) =
  TransportStr→UnivalentStr (transpMacroAction d) (transpMacroTransportStr d)
MacroUnivalentStr (foreign _ θ) = θ

-- Module for easy importing
module Macro ℓ (d : Desc ℓ) where

  structure = MacroStructure d
  equiv = MacroEquivStr d
  univalent = MacroUnivalentStr d

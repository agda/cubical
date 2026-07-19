{-

Descriptor language for easily defining structures

-}
{-# OPTIONS --no-exact-split #-}
module Cubical.Structures.Macro where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.SIP
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe

open import Cubical.Structures.Axioms
open import Cubical.Structures.Constant
open import Cubical.Structures.Function
open import Cubical.Structures.Maybe
open import Cubical.Structures.Parameterized
open import Cubical.Structures.Pointed
open import Cubical.Structures.Product

{- Transport structures -}

data TranspDesc (ℓ : Level) : Level → Typeω where
  -- constant structure: X ↦ A
  constant : ∀ {ℓ₁} (A : Type ℓ₁) → TranspDesc ℓ ℓ₁
  -- pointed structure: X ↦ X
  var : TranspDesc ℓ ℓ
  -- product of structures S,T : X ↦ (S X × T X)
  _,_ : ∀ {ℓ₁ ℓ₂} (d₀ : TranspDesc ℓ ℓ₁) (d₁ : TranspDesc ℓ ℓ₂) → TranspDesc ℓ (ℓ-max ℓ₁ ℓ₂)
  -- functions between structures S,T: X ↦ (S X → T X)
  function : ∀ {ℓ₁ ℓ₂} (d₀ : TranspDesc ℓ ℓ₁) (d₁ : TranspDesc ℓ ℓ₂) → TranspDesc ℓ (ℓ-max ℓ₁ ℓ₂)
  -- Maybe on a structure S: X ↦ Maybe (S X)
  maybe : ∀ {ℓ₁} → TranspDesc ℓ ℓ₁ → TranspDesc ℓ ℓ₁
  -- arbitrary transport structure
  foreign : ∀ {ℓ₁} {S : Type ℓ → Type ℓ₁} (α : EquivAction S) → TransportStr α → TranspDesc ℓ ℓ₁

-- Structure defined by a transport descriptor
TranspMacroStructure : ∀ {ℓ ℓ₁} → TranspDesc ℓ ℓ₁ → Type ℓ → Type ℓ₁
TranspMacroStructure (constant A) X = A
TranspMacroStructure var X = X
TranspMacroStructure (d₀ , d₁) X = TranspMacroStructure d₀ X × TranspMacroStructure d₁ X
TranspMacroStructure (function d₀ d₁) X = TranspMacroStructure d₀ X → TranspMacroStructure d₁ X
TranspMacroStructure (maybe d) = MaybeStructure (TranspMacroStructure d)
TranspMacroStructure (foreign {S = S} α τ) = S

-- Action defined by a transport descriptor
transpMacroAction : ∀ {ℓ ℓ₁} (d : TranspDesc ℓ ℓ₁) → EquivAction (TranspMacroStructure d)
transpMacroAction (constant A) = constantEquivAction A
transpMacroAction var = pointedEquivAction
transpMacroAction (d₀ , d₁) = productEquivAction (transpMacroAction d₀) (transpMacroAction d₁)
transpMacroAction (function d₀ d₁) =
  functionEquivAction (transpMacroAction d₀) (transpMacroAction d₁)
transpMacroAction (maybe d) = maybeEquivAction (transpMacroAction d)
transpMacroAction (foreign α _) = α

-- Action defines a transport structure
transpMacroTransportStr : ∀ {ℓ ℓ₁} (d : TranspDesc ℓ ℓ₁) → TransportStr (transpMacroAction d)
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

mutual
  data Desc (ℓ : Level) : Level → Level → Typeω where
    -- constant structure: X ↦ A
    constant : ∀ {ℓ₁} (A : Type ℓ₁) → Desc ℓ ℓ₁ ℓ₁
    -- pointed structure: X ↦ X
    var : Desc ℓ ℓ ℓ
    -- product of structures S,T : X ↦ (S X × T X)
    _,_ : ∀ {ℓ₁ ℓ₁' ℓ₂ ℓ₂'} (d₀ : Desc ℓ ℓ₁ ℓ₁') (d₁ : Desc ℓ ℓ₂ ℓ₂')
      → Desc ℓ (ℓ-max ℓ₁ ℓ₂) (ℓ-max ℓ₁' ℓ₂')
    -- functions between structures S,T : X ↦ (S X → T X)
    function : ∀ {ℓ₁ ℓ₁' ℓ₂ ℓ₂'} (d₀ : Desc ℓ ℓ₁ ℓ₁') (d₁ : Desc ℓ ℓ₂ ℓ₂')
      → Desc ℓ (ℓ-max ℓ₁ ℓ₂) (ℓ-max ℓ₁ (ℓ-max ℓ₁' ℓ₂'))
    -- functions between structures S,T where S is functorial : X ↦ (S X → T X)
    function+ : ∀ {ℓ₁ ℓ₂ ℓ₂'} (d₀ : TranspDesc ℓ ℓ₁) (d₁ : Desc ℓ ℓ₂ ℓ₂') → Desc ℓ (ℓ-max ℓ₁ ℓ₂) (ℓ-max ℓ₁ ℓ₂')
    -- Maybe on a structure S: X ↦ Maybe (S X)
    maybe : ∀ {ℓ₁ ℓ₁'} → Desc ℓ ℓ₁ ℓ₁' → Desc ℓ ℓ₁ ℓ₁'
    -- add axioms to a structure
    axioms : ∀ {ℓ₁ ℓ₁' ℓ₂} (d : Desc ℓ ℓ₁ ℓ₁') (ax : ∀ X → MacroStructure d X → Type ℓ₂)
      → (∀ X s → isProp (ax X s))
      → Desc ℓ (ℓ-max ℓ₁ ℓ₂) ℓ₁'
    -- univalent structure from transport structure
    transpDesc : ∀ {ℓ₁} → TranspDesc ℓ ℓ₁ → Desc ℓ ℓ₁ ℓ₁
    -- arbitrary univalent notion of structure
    foreign : ∀ {ℓ₁ ℓ₁'} {S : Type ℓ → Type ℓ₁} (ι : StrEquiv S ℓ₁') → UnivalentStr S ι → Desc ℓ ℓ₁ ℓ₁'

  infixr 4 _,_

  -- Structure defined by a descriptor
  MacroStructure : ∀ {ℓ ℓ₁ ℓ₁'} → Desc ℓ ℓ₁ ℓ₁' → Type ℓ → Type ℓ₁
  MacroStructure (constant A) X = A
  MacroStructure var X = X
  MacroStructure (d₀ , d₁) X = MacroStructure d₀ X × MacroStructure d₁ X
  MacroStructure (function+ d₀ d₁) X = TranspMacroStructure d₀ X → MacroStructure d₁ X
  MacroStructure (function d₀ d₁) X = MacroStructure d₀ X → MacroStructure d₁ X
  MacroStructure (maybe d) = MaybeStructure (MacroStructure d)
  MacroStructure (axioms d ax _) = AxiomsStructure (MacroStructure d) ax
  MacroStructure (transpDesc d) = TranspMacroStructure d
  MacroStructure (foreign {S = S} _ _) = S

-- Notion of structured equivalence defined by a descriptor
MacroEquivStr : ∀ {ℓ ℓ₁ ℓ₁'} → (d : Desc ℓ ℓ₁ ℓ₁') → StrEquiv (MacroStructure d) ℓ₁'
MacroEquivStr (constant A) = ConstantEquivStr A
MacroEquivStr var = PointedEquivStr
MacroEquivStr (d₀ , d₁) = ProductEquivStr (MacroEquivStr d₀) (MacroEquivStr d₁)
MacroEquivStr (function+ d₀ d₁) = FunctionEquivStr+ (transpMacroAction d₀) (MacroEquivStr d₁)
MacroEquivStr (function d₀ d₁) = FunctionEquivStr (MacroEquivStr d₀) (MacroEquivStr d₁)
MacroEquivStr (maybe d) = MaybeEquivStr (MacroEquivStr d)
MacroEquivStr (axioms d ax _) = AxiomsEquivStr (MacroEquivStr d) ax
MacroEquivStr (transpDesc d) = EquivAction→StrEquiv (transpMacroAction d)
MacroEquivStr (foreign ι _) = ι

-- Proof that structure induced by descriptor is univalent
MacroUnivalentStr : ∀ {ℓ ℓ₁ ℓ₁'} → (d : Desc ℓ ℓ₁ ℓ₁') → UnivalentStr (MacroStructure d) (MacroEquivStr d)
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
MacroUnivalentStr (axioms d _ isPropAx) = axiomsUnivalentStr (MacroEquivStr d) isPropAx (MacroUnivalentStr d)
MacroUnivalentStr (transpDesc d) =
  TransportStr→UnivalentStr (transpMacroAction d) (transpMacroTransportStr d)
MacroUnivalentStr (foreign _ θ) = θ

-- Module for easy importing
module Macro ℓ {ℓ₁ ℓ₁'} (d : Desc ℓ ℓ₁ ℓ₁') where

  structure = MacroStructure d
  equiv = MacroEquivStr d
  univalent = MacroUnivalentStr d

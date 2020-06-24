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
open import Cubical.Structures.Maybe
open import Cubical.Structures.NAryOp
open import Cubical.Structures.Parameterized
open import Cubical.Structures.Pointed
open import Cubical.Structures.Product
open import Cubical.Structures.Functorial

data FuncDesc (ℓ : Level) : Typeω where
  -- constant structure: X ↦ A
  constant : ∀ {ℓ'} → Type ℓ' → FuncDesc ℓ
  -- pointed structure: X ↦ X
  var : FuncDesc ℓ
  -- join of structures S,T : X ↦ (S X × T X)
  _,_ : FuncDesc ℓ  → FuncDesc ℓ  → FuncDesc ℓ
  -- structure S parameterized by constant A : X ↦ (A → S X)
  param : ∀ {ℓ'} → (A : Type ℓ') → FuncDesc ℓ  → FuncDesc ℓ
  -- structure S parameterized by variable argument: X ↦ (X → S X)
  maybe : FuncDesc ℓ → FuncDesc ℓ

data Desc (ℓ : Level) : Typeω where
  -- constant structure: X ↦ A
  constant : ∀ {ℓ'} → Type ℓ' → Desc ℓ
  -- pointed structure: X ↦ X
  var : Desc ℓ
  -- join of structures S,T : X ↦ (S X × T X)
  _,_ : Desc ℓ  → Desc ℓ  → Desc ℓ
  -- structure S parameterized by constant A : X ↦ (A → S X)
  param : ∀ {ℓ'} → (A : Type ℓ') → Desc ℓ  → Desc ℓ
  -- structure S parameterized by variable argument: X ↦ (X → S X)
  recvar : Desc ℓ  → Desc ℓ
  -- Maybe on a structure S: X ↦ Maybe (S X)
  maybe : Desc ℓ → Desc ℓ
  -- SNS from functorial action
  functorial : FuncDesc ℓ → Desc ℓ
  -- arbitrary standard notion of structure
  foreign : ∀ {ℓ' ℓ''} {S : Type ℓ → Type ℓ'} (ι : StrEquiv S ℓ'') → UnivalentStr S ι → Desc ℓ

infixr 4 _,_

{- Functorial structures -}

funcMacroLevel : ∀ {ℓ} → FuncDesc ℓ → Level
funcMacroLevel (constant {ℓ'} x) = ℓ'
funcMacroLevel {ℓ} var = ℓ
funcMacroLevel {ℓ} (d₀ , d₁) = ℓ-max (funcMacroLevel d₀) (funcMacroLevel d₁)
funcMacroLevel (param {ℓ'} A d) = ℓ-max ℓ' (funcMacroLevel d)
funcMacroLevel (maybe d) = funcMacroLevel d

-- Structure defined by a functorial descriptor
FuncMacroStructure : ∀ {ℓ} (d : FuncDesc ℓ) → Type ℓ → Type (funcMacroLevel d)
FuncMacroStructure (constant A) X = A
FuncMacroStructure var X = X
FuncMacroStructure (d₀ , d₁) X = FuncMacroStructure d₀ X × FuncMacroStructure d₁ X
FuncMacroStructure (param A d) X = A → FuncMacroStructure d X
FuncMacroStructure (maybe d) = MaybeStructure (FuncMacroStructure d)

-- Action defined by a functorial descriptor
funcMacroAction : ∀ {ℓ} (d : FuncDesc ℓ)
  {X Y : Type ℓ} → (X → Y) → FuncMacroStructure d X → FuncMacroStructure d Y
funcMacroAction (constant A) _ = idfun A
funcMacroAction var f = f
funcMacroAction (d₀ , d₁) f (s₀ , s₁) = funcMacroAction d₀ f s₀ , funcMacroAction d₁ f s₁
funcMacroAction (param A d) f s a = funcMacroAction d f (s a)
funcMacroAction (maybe d) f = map-Maybe (funcMacroAction d f)

-- Proof that the action preserves the identity
funcMacroId : ∀ {ℓ} (d : FuncDesc ℓ)
  {X : Type ℓ} → ∀ s → funcMacroAction d (idfun X) s ≡ s
funcMacroId (constant A) _ = refl
funcMacroId var _ = refl
funcMacroId (d₀ , d₁) (s₀ , s₁) = ΣPath≃PathΣ .fst (funcMacroId d₀ s₀ , funcMacroId d₁ s₁)
funcMacroId (param A d) s = funExt λ a → funcMacroId d (s a)
funcMacroId (maybe d) s = cong₂ map-Maybe (funExt (funcMacroId d)) refl ∙ map-Maybe-id s

{- General structures -}

macroStrLevel : ∀ {ℓ} → Desc ℓ → Level
macroStrLevel (constant {ℓ'} x) = ℓ'
macroStrLevel {ℓ} var = ℓ
macroStrLevel {ℓ} (d₀ , d₁) = ℓ-max (macroStrLevel d₀) (macroStrLevel d₁)
macroStrLevel (param {ℓ'} A d) = ℓ-max ℓ' (macroStrLevel d)
macroStrLevel {ℓ} (recvar d) = ℓ-max ℓ (macroStrLevel d)
macroStrLevel (maybe d) = macroStrLevel d
macroStrLevel (functorial d) = funcMacroLevel d
macroStrLevel (foreign {ℓ'} _ _) = ℓ'

macroEquivLevel : ∀ {ℓ} → Desc ℓ → Level
macroEquivLevel (constant {ℓ'} x) = ℓ'
macroEquivLevel {ℓ} var = ℓ
macroEquivLevel {ℓ} (d₀ , d₁) = ℓ-max (macroEquivLevel d₀) (macroEquivLevel d₁)
macroEquivLevel (param {ℓ'} A d) = ℓ-max ℓ' (macroEquivLevel d)
macroEquivLevel {ℓ} (recvar d) = ℓ-max ℓ (macroEquivLevel d)
macroEquivLevel (maybe d) = macroEquivLevel d
macroEquivLevel (functorial d) = funcMacroLevel d
macroEquivLevel (foreign {ℓ'' = ℓ''} _ _) = ℓ''

-- Structure defined by a descriptor
MacroStructure : ∀ {ℓ} (d : Desc ℓ) → Type ℓ → Type (macroStrLevel d)
MacroStructure (constant A) X = A
MacroStructure var X = X
MacroStructure (d₀ , d₁) X = MacroStructure d₀ X × MacroStructure d₁ X
MacroStructure (param A d) X = A → MacroStructure d X
MacroStructure (recvar d) X = X → MacroStructure d X
MacroStructure (maybe d) = MaybeStructure (MacroStructure d)
MacroStructure (functorial d) = FuncMacroStructure d
MacroStructure (foreign {S = S} _ _) = S

-- Notion of structured equivalence defined by a descriptor
MacroEquivStr : ∀ {ℓ} → (d : Desc ℓ) → StrEquiv {ℓ} (MacroStructure d) (macroEquivLevel d)
MacroEquivStr (constant A) = ConstantEquivStr A
MacroEquivStr var = PointedEquivStr
MacroEquivStr (d₀ , d₁) = ProductEquivStr (MacroEquivStr d₀) (MacroEquivStr d₁)
MacroEquivStr (param A d) = ParamEquivStr A λ _ → MacroEquivStr d
MacroEquivStr (recvar d) = UnaryFunEquivStr (MacroEquivStr d)
MacroEquivStr (maybe d) = MaybeEquivStr (MacroEquivStr d)
MacroEquivStr (functorial d) = FunctorialEquivStr (funcMacroAction d)
MacroEquivStr (foreign ι _) = ι

-- Proof that structure induced by descriptor is univalent
MacroUnivalentStr : ∀ {ℓ} → (d : Desc ℓ) → UnivalentStr (MacroStructure d) (MacroEquivStr d)
MacroUnivalentStr (constant A) = constantUnivalentStr A
MacroUnivalentStr var = pointedUnivalentStr
MacroUnivalentStr (d₀ , d₁) =
  ProductUnivalentStr (MacroEquivStr d₀) (MacroUnivalentStr d₀) (MacroEquivStr d₁) (MacroUnivalentStr d₁)
MacroUnivalentStr (param A d) = ParamUnivalentStr A (λ _ → MacroEquivStr d) (λ _ → MacroUnivalentStr d)
MacroUnivalentStr (recvar d) = unaryFunUnivalentStr (MacroEquivStr d) (MacroUnivalentStr d)
MacroUnivalentStr (maybe d) = maybeUnivalentStr (MacroEquivStr d) (MacroUnivalentStr d)
MacroUnivalentStr (functorial d) = functorialUnivalentStr (funcMacroAction d) (funcMacroId d)
MacroUnivalentStr (foreign _ θ) = θ

-- Module for easy importing
module Macro ℓ (d : Desc ℓ) where

  structure = MacroStructure d
  equiv = MacroEquivStr d
  univalent = MacroUnivalentStr d

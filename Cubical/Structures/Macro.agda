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

funcMacro-structure-level : ∀ {ℓ} → FuncDesc ℓ → Level
funcMacro-structure-level (constant {ℓ'} x) = ℓ'
funcMacro-structure-level {ℓ} var = ℓ
funcMacro-structure-level {ℓ} (d₀ , d₁) = ℓ-max (funcMacro-structure-level d₀) (funcMacro-structure-level d₁)
funcMacro-structure-level (param {ℓ'} A d) = ℓ-max ℓ' (funcMacro-structure-level d)
funcMacro-structure-level (maybe d) = funcMacro-structure-level d

-- Structure defined by a functorial descriptor
funcMacro-structure : ∀ {ℓ} (d : FuncDesc ℓ) → Type ℓ → Type (funcMacro-structure-level d)
funcMacro-structure (constant A) X = A
funcMacro-structure var X = X
funcMacro-structure (d₀ , d₁) X = funcMacro-structure d₀ X × funcMacro-structure d₁ X
funcMacro-structure (param A d) X = A → funcMacro-structure d X
funcMacro-structure (maybe d) = MaybeStructure (funcMacro-structure d)

-- Action defined by a functorial descriptor
funcMacro-action : ∀ {ℓ} (d : FuncDesc ℓ)
  {X Y : Type ℓ} → (X → Y) → funcMacro-structure d X → funcMacro-structure d Y
funcMacro-action (constant A) _ = idfun A
funcMacro-action var f = f
funcMacro-action (d₀ , d₁) f (s₀ , s₁) = funcMacro-action d₀ f s₀ , funcMacro-action d₁ f s₁
funcMacro-action (param A d) f s a = funcMacro-action d f (s a)
funcMacro-action (maybe d) f = map-Maybe (funcMacro-action d f)

-- Proof that the action preserves the identity

funcMacro-id : ∀ {ℓ} (d : FuncDesc ℓ)
  {X : Type ℓ} → ∀ s → funcMacro-action d (idfun X) s ≡ s
funcMacro-id (constant A) _ = refl
funcMacro-id var _ = refl
funcMacro-id (d₀ , d₁) (s₀ , s₁) = ΣPath≃PathΣ .fst (funcMacro-id d₀ s₀ , funcMacro-id d₁ s₁)
funcMacro-id (param A d) s = funExt λ a → funcMacro-id d (s a)
funcMacro-id (maybe d) s = cong₂ map-Maybe (funExt (funcMacro-id d)) refl ∙ map-Maybe-id s

{- General structures -}

macro-structure-level : ∀ {ℓ} → Desc ℓ → Level
macro-structure-level (constant {ℓ'} x) = ℓ'
macro-structure-level {ℓ} var = ℓ
macro-structure-level {ℓ} (d₀ , d₁) = ℓ-max (macro-structure-level d₀) (macro-structure-level d₁)
macro-structure-level (param {ℓ'} A d) = ℓ-max ℓ' (macro-structure-level d)
macro-structure-level {ℓ} (recvar d) = ℓ-max ℓ (macro-structure-level d)
macro-structure-level (maybe d) = macro-structure-level d
macro-structure-level (functorial d) = funcMacro-structure-level d
macro-structure-level (foreign {ℓ'} _ _) = ℓ'

macro-iso-level : ∀ {ℓ} → Desc ℓ → Level
macro-iso-level (constant {ℓ'} x) = ℓ'
macro-iso-level {ℓ} var = ℓ
macro-iso-level {ℓ} (d₀ , d₁) = ℓ-max (macro-iso-level d₀) (macro-iso-level d₁)
macro-iso-level (param {ℓ'} A d) = ℓ-max ℓ' (macro-iso-level d)
macro-iso-level {ℓ} (recvar d) = ℓ-max ℓ (macro-iso-level d)
macro-iso-level (maybe d) = macro-iso-level d
macro-iso-level (functorial d) = funcMacro-structure-level d
macro-iso-level (foreign {ℓ'' = ℓ''} _ _) = ℓ''

-- Structure defined by a descriptor
macro-structure : ∀ {ℓ} (d : Desc ℓ) → Type ℓ → Type (macro-structure-level d)
macro-structure (constant A) X = A
macro-structure var X = X
macro-structure (d₀ , d₁) X = macro-structure d₀ X × macro-structure d₁ X
macro-structure (param A d) X = A → macro-structure d X
macro-structure (recvar d) X = X → macro-structure d X
macro-structure (maybe d) = MaybeStructure (macro-structure d)
macro-structure (functorial d) = funcMacro-structure d
macro-structure (foreign {S = S} _ _) = S

-- Notion of structured isomorphism defined by a descriptor
macro-iso : ∀ {ℓ} → (d : Desc ℓ) → StrEquiv {ℓ} (macro-structure d) (macro-iso-level d)
macro-iso (constant A) = ConstantEquivStr A
macro-iso var = PointedEquivStr
macro-iso (d₀ , d₁) = ProductEquivStr (macro-iso d₀) (macro-iso d₁)
macro-iso (param A d) = ParamEquivStr A λ _ → macro-iso d
macro-iso (recvar d) = UnaryFunEquivStr (macro-iso d)
macro-iso (maybe d) = MaybeEquivStr (macro-iso d)
macro-iso (functorial d) = FunctorialEquivStr (funcMacro-action d)
macro-iso (foreign ι _) = ι

-- Proof that structure induced by descriptor is a standard notion of structure
macro-is-SNS : ∀ {ℓ} → (d : Desc ℓ) → UnivalentStr (macro-structure d) (macro-iso d)
macro-is-SNS (constant A) = constantUnivalentStr A
macro-is-SNS var = pointedUnivalentStr
macro-is-SNS (d₀ , d₁) = ProductUnivalentStr (macro-iso d₀) (macro-is-SNS d₀) (macro-iso d₁) (macro-is-SNS d₁)
macro-is-SNS (param A d) = ParamUnivalentStr A (λ _ → macro-iso d) (λ _ → macro-is-SNS d)
macro-is-SNS (recvar d) = unaryFunUnivalentStr (macro-iso d) (macro-is-SNS d)
macro-is-SNS (maybe d) = maybeUnivalentStr (macro-iso d) (macro-is-SNS d)
macro-is-SNS (functorial d) = functorialUnivalentStr (funcMacro-action d) (funcMacro-id d)
macro-is-SNS (foreign _ θ) = θ

-- Module for easy importing
module Macro ℓ (d : Desc ℓ) where

  structure = macro-structure d
  iso = macro-iso d
  isSNS = macro-is-SNS d

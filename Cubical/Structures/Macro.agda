{-# OPTIONS --cubical --no-exact-split --safe #-}
module Cubical.Structures.Macro where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.SIP renaming (SNS-PathP to SNS)
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Sigma

open import Cubical.Structures.Constant
open import Cubical.Structures.Pointed
open import Cubical.Structures.NAryOp
open import Cubical.Structures.Parameterized
open import Cubical.Structures.Functorial

data Desc (ℓ : Level) : Typeω where
  constant : ∀ {ℓ'} → Type ℓ' → Desc ℓ
  var : Desc ℓ
  _,_ : Desc ℓ  → Desc ℓ  → Desc ℓ
  param : ∀ {ℓ'} → (A : Type ℓ') → Desc ℓ  → Desc ℓ
  recvar : Desc ℓ  → Desc ℓ
  functorial : ∀ {ℓ'} {S : Type ℓ → Type ℓ'}
    (F : ∀ {X Y} → (X → Y) → S X → S Y) → (∀ {X} s → F (idfun X) s ≡ s) → Desc ℓ
  foreign : ∀ {ℓ' ℓ''} {S : Type ℓ → Type ℓ'} (ι : StrIso S ℓ'') → SNS S ι → Desc ℓ

infixr 4 _,_

macro-structure-level : ∀ {ℓ} → Desc ℓ → Level
macro-structure-level (constant {ℓ'} x) = ℓ'
macro-structure-level {ℓ} var = ℓ
macro-structure-level {ℓ} (d₀ , d₁) = ℓ-max (macro-structure-level d₀) (macro-structure-level d₁)
macro-structure-level (param {ℓ'} A d) = ℓ-max ℓ' (macro-structure-level d)
macro-structure-level {ℓ} (recvar d) = ℓ-max ℓ (macro-structure-level d)
macro-structure-level (functorial {ℓ'} _ _) = ℓ'
macro-structure-level (foreign {ℓ'} _ _) = ℓ'

macro-structure : ∀ {ℓ} → (d : Desc ℓ) → Type ℓ → Type (macro-structure-level d)
macro-structure (constant A) X = A
macro-structure var X = X
macro-structure (d₀ , d₁) X = macro-structure d₀ X × macro-structure d₁ X
macro-structure (param A d) X = A → macro-structure d X
macro-structure (recvar d) X = X → macro-structure d X
macro-structure (functorial {S = S} _ _) = S
macro-structure (foreign {S = S} _ _) = S

macro-iso-level : ∀ {ℓ} → Desc ℓ → Level
macro-iso-level (constant {ℓ'} x) = ℓ'
macro-iso-level {ℓ} var = ℓ
macro-iso-level {ℓ} (d₀ , d₁) = ℓ-max (macro-iso-level d₀) (macro-iso-level d₁)
macro-iso-level (param {ℓ'} A d) = ℓ-max ℓ' (macro-iso-level d)
macro-iso-level {ℓ} (recvar d) = ℓ-max ℓ (macro-iso-level d)
macro-iso-level (functorial {ℓ' = ℓ'} _ _) = ℓ'
macro-iso-level (foreign {ℓ'' = ℓ''} _ _) = ℓ''

macro-iso : ∀ {ℓ} → (d : Desc ℓ) → StrIso {ℓ} (macro-structure d) (macro-iso-level d)
macro-iso (constant A) = constant-iso A
macro-iso var = pointed-iso
macro-iso (d₀ , d₁) = join-iso (macro-iso d₀) (macro-iso d₁)
macro-iso (param A d) = parameterized-iso A λ _ → macro-iso d
macro-iso (recvar d) = unaryFunIso (macro-iso d)
macro-iso (functorial F _) = functorial-iso F
macro-iso (foreign ι _) = ι

macro-is-SNS : ∀ {ℓ} → (d : Desc ℓ) → SNS (macro-structure d) (macro-iso d)
macro-is-SNS (constant A) = constant-is-SNS A
macro-is-SNS var = pointed-is-SNS
macro-is-SNS (d₀ , d₁) = join-SNS (macro-iso d₀) (macro-is-SNS d₀) (macro-iso d₁) (macro-is-SNS d₁)
macro-is-SNS (param A d) = Parameterized-is-SNS A (λ _ → macro-iso d) (λ _ → macro-is-SNS d)
macro-is-SNS (recvar d) = unaryFunSNS (macro-iso d) (macro-is-SNS d)
macro-is-SNS (functorial F η) = functorial-is-SNS F η
macro-is-SNS (foreign _ θ) = θ

module Macro ℓ (d : Desc ℓ) where

  structure = macro-structure d
  iso = macro-iso d
  isSNS = macro-is-SNS d

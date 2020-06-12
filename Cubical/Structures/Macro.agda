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

data Desc : Typeω where
  constant : ∀ {ℓ} → Type ℓ → Desc
  var : Desc
  _,_ : Desc → Desc → Desc
  param : ∀ {ℓ} → (A : Type ℓ) → Desc → Desc
  recvar : Desc → Desc

infixr 4 _,_

ℓ-desc : Level → Desc → Level
ℓ-desc ℓ (constant {ℓ = ℓ'} x) = ℓ'
ℓ-desc ℓ var = ℓ
ℓ-desc ℓ (d₀ , d₁) = ℓ-max (ℓ-desc ℓ d₀) (ℓ-desc ℓ d₁)
ℓ-desc ℓ (param {ℓ = ℓ'} A d) = ℓ-max ℓ' (ℓ-desc ℓ d)
ℓ-desc ℓ (recvar d) = ℓ-max ℓ (ℓ-desc ℓ d)

macro-structure : (d : Desc) → ∀ {ℓ} → Type ℓ → Type (ℓ-desc ℓ d)
macro-structure (constant A) X = A
macro-structure var X = X
macro-structure (d₀ , d₁) X = macro-structure d₀ X × macro-structure d₁ X
macro-structure (param A d) X = A → macro-structure d X
macro-structure (recvar d) X = X → macro-structure d X

macro-iso : (d : Desc) → ∀ {ℓ} → StrIso {ℓ} (macro-structure d) (ℓ-desc ℓ d)
macro-iso (constant A) = constant-iso A
macro-iso var = pointed-iso
macro-iso (d₀ , d₁) = join-iso (macro-iso d₀) (macro-iso d₁)
macro-iso (param A d) = parameterized-iso A λ _ → macro-iso d
macro-iso (recvar d) = unaryFunIso (macro-iso d)

macro-is-SNS : (d : Desc) → ∀ {ℓ} → SNS {ℓ} (macro-structure d) (macro-iso d)
macro-is-SNS (constant A) = constant-is-SNS A
macro-is-SNS var = pointed-is-SNS
macro-is-SNS (d₀ , d₁) = join-SNS (macro-iso d₀) (macro-is-SNS d₀) (macro-iso d₁) (macro-is-SNS d₁)
macro-is-SNS (param A d) = Parameterized-is-SNS A (λ _ → macro-iso d) (λ _ → macro-is-SNS d)
macro-is-SNS (recvar d) = unaryFunSNS (macro-iso d) (macro-is-SNS d)

module Macro ℓ (d : Desc) where

  structure = macro-structure d {ℓ}
  iso = macro-iso d {ℓ}
  isSNS = macro-is-SNS d {ℓ}
  

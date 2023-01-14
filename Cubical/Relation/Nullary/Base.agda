{-# OPTIONS --safe #-}
module Cubical.Relation.Nullary.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Functions.Fixpoint

open import Cubical.Data.Empty as ⊥
open import Cubical.HITs.PropositionalTruncation.Base

private
  variable
    ℓ  : Level
    A  : Type ℓ

-- Negation
infix 3 ¬_

¬_ : Type ℓ → Type ℓ
¬ A = A → ⊥

-- Decidable types (inspired by standard library)
data Dec (P : Type ℓ) : Type ℓ where
  yes : ( p :   P) → Dec P
  no  : (¬p : ¬ P) → Dec P

decRec : ∀ {ℓ ℓ'} {P : Type ℓ} {A : Type ℓ'} → (P → A) → (¬ P → A) → (Dec P) → A
decRec ifyes ifno (yes p) = ifyes p
decRec ifyes ifno (no ¬p) = ifno ¬p

NonEmpty : Type ℓ → Type ℓ
NonEmpty A = ¬ ¬ A

Stable : Type ℓ → Type ℓ
Stable A = NonEmpty A → A

-- reexport propositional truncation for uniformity
open Cubical.HITs.PropositionalTruncation.Base
  using (∥_∥₁) public

SplitSupport : Type ℓ → Type ℓ
SplitSupport A = ∥ A ∥₁ → A

Collapsible : Type ℓ → Type ℓ
Collapsible A = Σ[ f ∈ (A → A) ] 2-Constant f

Populated ⟪_⟫ : Type ℓ → Type ℓ
Populated A = (f : Collapsible A) → Fixpoint (f .fst)
⟪_⟫ = Populated

PStable : Type ℓ → Type ℓ
PStable A = ⟪ A ⟫ → A

onAllPaths : (Type ℓ → Type ℓ) → Type ℓ → Type ℓ
onAllPaths S A = (x y : A) → S (x ≡ y)

Separated : Type ℓ → Type ℓ
Separated = onAllPaths Stable

HSeparated : Type ℓ → Type ℓ
HSeparated = onAllPaths SplitSupport

Collapsible≡ : Type ℓ → Type ℓ
Collapsible≡ = onAllPaths Collapsible

PStable≡ : Type ℓ → Type ℓ
PStable≡ = onAllPaths PStable

Discrete : Type ℓ → Type ℓ
Discrete = onAllPaths Dec

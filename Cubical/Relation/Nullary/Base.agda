{-# OPTIONS --cubical --safe #-}
module Cubical.Relation.Nullary.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

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

NonEmpty : Type ℓ → Type ℓ
NonEmpty A = ¬ ¬ A

Stable : Type ℓ → Type ℓ
Stable A = NonEmpty A → A

-- reexport propositional truncation for uniformity
open Cubical.HITs.PropositionalTruncation.Base
  using (∥_∥) public

SplitSupport HStable : Type ℓ → Type ℓ
SplitSupport A = ∥ A ∥ → A
HStable = SplitSupport

Collapsible : Type ℓ → Type ℓ
Collapsible A = Σ[ f ∈ (A → A) ] 2-Constant f

Populated : Type ℓ → Type ℓ
Populated A = (f : Collapsible A) → Fixpoint (f .fst)

PStable : Type ℓ → Type ℓ
PStable A = Populated A → A

Separated Stable≡ : Type ℓ → Type ℓ
Separated A = (x y : A) → Stable (x ≡ y)
Stable≡ = Separated

HSeparated HStable≡ : Type ℓ → Type ℓ
HSeparated A = (x y : A) → HStable (x ≡ y)
HStable≡ = HSeparated

Collapsible≡ : Type ℓ → Type ℓ
Collapsible≡ A = (x y : A) → Collapsible (x ≡ y)

PStable≡ : Type ℓ → Type ℓ
PStable≡ A = (x y : A) → PStable (x ≡ y)

Discrete : Type ℓ → Type ℓ
Discrete A = (x y : A) → Dec (x ≡ y)

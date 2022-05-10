{-# OPTIONS --safe #-}
module Cubical.Data.FinData.Order where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Bool.Base
open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary


open import Cubical.Data.FinData.Base
open import Cubical.Data.FinData.Properties

private
  variable
    ℓ : Level


-- Order relation:
_≤Fin_ : {n : ℕ} → Fin n → Fin n → Type
i ≤Fin j = (toℕ i) ≤ (toℕ j)

_<Fin_ : {n : ℕ} → Fin n → Fin n → Type
i <Fin j = (suc i) ≤Fin (weakenFin j)

open BinaryRelation
≤FinIsPropValued : ∀ {n : ℕ} → isPropValued (_≤Fin_ {n})
≤FinIsPropValued _ _ = isProp≤


-- inductive version
_≤'Fin_ : {n : ℕ} → Fin n → Fin n → Type
i ≤'Fin j = (toℕ i) ≤' (toℕ j)

_<'Fin_ : {n : ℕ} → Fin n → Fin n → Type
i <'Fin j = (suc i) ≤'Fin (weakenFin j)

open BinaryRelation
≤'FinIsPropValued : ∀ {n : ℕ} → isPropValued (_≤'Fin_ {n})
≤'FinIsPropValued _ _ = ≤'IsPropValued _ _

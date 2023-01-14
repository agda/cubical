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


data FinTrichotomy {n : ℕ} (i j : Fin n) : Type₀ where
  lt : i <'Fin j → FinTrichotomy i j
  eq : i ≡ j → FinTrichotomy i j
  gt : j <'Fin i → FinTrichotomy i j


FinTrichotomy-suc : {n : ℕ} {i j : Fin n} → FinTrichotomy i j → FinTrichotomy (suc i) (suc j)
FinTrichotomy-suc (lt i<j) = lt (s≤s i<j)
FinTrichotomy-suc (eq i=j) = eq (cong suc i=j)
FinTrichotomy-suc (gt j<i) = gt (s≤s j<i)

_≟Fin_ : {n : ℕ} (i j : Fin n) → FinTrichotomy i j
_≟Fin_ {n = ℕ.suc n} zero zero = eq refl
_≟Fin_ {n = ℕ.suc n} zero (suc j) = lt (s≤s z≤)
_≟Fin_ {n = ℕ.suc n} (suc i) zero = gt (s≤s z≤)
_≟Fin_ {n = ℕ.suc n} (suc i) (suc j) = FinTrichotomy-suc (i ≟Fin j)

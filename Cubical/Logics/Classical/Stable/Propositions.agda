{-# OPTIONS --safe #-}

module Cubical.Logics.Classical.Stable.Propositions where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure
open import Cubical.Data.Empty
open import Cubical.Relation.Nullary

private variable
  ℓ ℓ' : Level
  A B : Type ℓ

η : A → ¬ ¬ A
η a ¬a = ¬a a

isStableProp : Type ℓ → Type ℓ
isStableProp A = isEquiv (η {A = A})

¬¬Prop : ∀ ℓ → Type (ℓ-suc ℓ)
¬¬Prop ℓ = TypeWithStr ℓ isStableProp

{-# OPTIONS --cubical --safe #-}
module Cubical.Data.Bool.Base where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude

open import Cubical.Data.Empty

open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.DecidableEq

-- Obtain the booleans
open import Agda.Builtin.Bool public

infixr 6 _and_
infixr 5 _or_

not : Bool → Bool
not true = false
not false = true

_or_ : Bool → Bool → Bool
false or false = false
false or true  = true
true  or false = true
true  or true  = true

_and_ : Bool → Bool → Bool
false and false = false
false and true  = false
true  and false = false
true  and true  = true

caseBool : ∀ {ℓ} → {A : Type ℓ} → (a0 aS : A) → Bool → A
caseBool att aff true  = att
caseBool att aff false = aff

_≟_ : Discrete Bool
false ≟ false = yes refl
false ≟ true  = no λ p → subst (caseBool ⊥ Bool) p true
true  ≟ false = no λ p → subst (caseBool Bool ⊥) p true
true  ≟ true  = yes refl

Dec→Bool : ∀ {ℓ} {A : Type ℓ} → Dec A → Bool
Dec→Bool (yes p) = true
Dec→Bool (no ¬p) = false

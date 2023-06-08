{-# OPTIONS --safe #-}
module Cubical.Data.Bool.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Empty
open import Cubical.Data.Sum.Base
open import Cubical.Data.Unit.Base

open import Cubical.Relation.Nullary.Base

-- Obtain the booleans
open import Agda.Builtin.Bool public

private
  variable
    ℓ : Level
    A : Type ℓ

infixr 6 _and_
infixr 5 _or_
infix  0 if_then_else_

not : Bool → Bool
not true = false
not false = true

_or_ : Bool → Bool → Bool
false or x = x
true  or _ = true

_and_ : Bool → Bool → Bool
false and _ = false
true  and x = x

-- xor / mod-2 addition
_⊕_ : Bool → Bool → Bool
false ⊕ x = x
true  ⊕ x = not x

if_then_else_ : Bool → A → A → A
if true  then x else y = x
if false then x else y = y

_≟_ : Discrete Bool
false ≟ false = yes refl
false ≟ true  = no λ p → subst (λ b → if b then ⊥ else Bool) p true
true  ≟ false = no λ p → subst (λ b → if b then Bool else ⊥) p true
true  ≟ true  = yes refl

Dec→Bool : Dec A → Bool
Dec→Bool (yes p) = true
Dec→Bool (no ¬p) = false

-- Helpers for automatic proof
Bool→Type : Bool → Type₀
Bool→Type true = Unit
Bool→Type false = ⊥

Bool→Type* : Bool → Type ℓ
Bool→Type* true = Unit*
Bool→Type* false = ⊥*

True : Dec A → Type₀
True Q = Bool→Type (Dec→Bool Q)

False : Dec A → Type₀
False Q = Bool→Type (not (Dec→Bool Q))

toWitness : {Q : Dec A} → True Q → A
toWitness {Q = yes p} _ = p

toWitnessFalse : {Q : Dec A} → False Q → ¬ A
toWitnessFalse {Q = no ¬p} _ = ¬p

dichotomyBool : (x : Bool) → (x ≡ true) ⊎ (x ≡ false)
dichotomyBool true  = inl refl
dichotomyBool false = inr refl

dichotomyBoolSym : (x : Bool) → (x ≡ false) ⊎ (x ≡ true)
dichotomyBoolSym false = inl refl
dichotomyBoolSym true = inr refl

-- TODO: this should be uncommented and implemented using instance arguments
-- _==_ : {dA : Discrete A} → A → A → Bool
-- _==_ {dA = dA} x y = Dec→Bool (dA x y)

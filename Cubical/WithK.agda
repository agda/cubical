{- Cubical Agda with K

This file demonstrates the incompatibility of the --cubical
and --with-K flags, relying on the well-known incosistency of K with
univalence.

The --safe flag can be used to prevent accidentally mixing such
incompatible flags.

-}

{-# OPTIONS --with-K #-}

module Cubical.WithK where

open import Cubical.Data.Equality
open import Cubical.Data.Bool
open import Cubical.Data.Empty

private
 variable
  ℓ : Level
  A : Type ℓ
  x y : A

uip : (prf : x ≡ x) → Path _ prf refl
uip refl i = refl

transport-uip : (prf : A ≡ A) → Path _ (transportPath (eqToPath prf) x) x
transport-uip {x = x} prf =
  compPath (congPath (λ p → transportPath (eqToPath p) x) (uip prf)) (transportRefl x)

transport-not : Path _ (transportPath (eqToPath (pathToEq notEq)) true) false
transport-not = congPath (λ a → transportPath a true) (eqToPath-pathToEq notEq)

false-true : Path _ false true
false-true = compPath (symPath transport-not) (transport-uip (pathToEq notEq))

absurd : (X : Type) → X
absurd X = transportPath (congPath sel false-true) true
  where
    sel : Bool → Type
    sel false = Bool
    sel true = X

inconsistency : ⊥
inconsistency = absurd ⊥

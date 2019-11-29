{- Cubical Agda with K

This file demonstrates the incompatibility of the --cubical
and --with-K flags, relying on the well-known incosistency of K with
univalence.

The --safe flag can be used to prevent accidentally mixing such
incompatible flags.

-}

{-# OPTIONS --cubical --with-K #-}

module Cubical.WithK where

open import Cubical.Data.Equality
open import Cubical.Data.Bool
open import Cubical.Data.Empty


private
 variable
  ℓ : Level
  A : Set ℓ
  x y : A

uip : (prf : x ≡p x) → prf ≡c reflp
uip reflp i = reflp

transport-uip : (prf : A ≡p A) → transport (ptoc prf) x ≡c x
transport-uip {x = x} prf =
  cong (λ m → transport (ptoc m) x) (uip prf) ∙ transportRefl x

transport-not : transport (ptoc (ctop notEq)) true ≡c false
transport-not = cong (λ a → transport a true) (ptoc-ctop notEq)

false-true : false ≡c true
false-true = sym transport-not ∙ transport-uip (ctop notEq)

absurd : (X : Set) → X
absurd X = transport (cong sel false-true) true
  where
    sel : Bool → Set
    sel false = Bool
    sel true = X

inconsistency : ⊥
inconsistency = absurd ⊥

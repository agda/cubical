{- Cubical Agda with K

This file proves:

false-true : false ≡c true
absurd : (X : Set) → X
inconsistency : ⊥

The above proofs are based on two incompatible flags of Agda.

-}

{-# OPTIONS --cubical --with-K #-}

module Cubical.WithK.Properties where

open import Cubical.WithK.Base
open import Cubical.Data.Equality
open import Cubical.Data.Bool
open import Cubical.Data.Empty

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


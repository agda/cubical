{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.RingSolver.Utility where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Bool
open import Cubical.Data.Empty using (⊥) renaming (rec to recEmpty)
open import Cubical.Data.Sigma

open import Cubical.Relation.Nullary.Base

private
  variable
    ℓ ℓ′ : Level
byBoolAbsurdity : {Anything : Type ℓ} → false ≡ true → Anything
byBoolAbsurdity p = recEmpty (false≢true p)

byAbsurdity : {Anything : Type ℓ} → ⊥ → Anything
byAbsurdity x = recEmpty x

extract : (P Q : Bool)
              → P and Q ≡ true
              → (P ≡ true) × (Q ≡ true)
extract false false eq = byBoolAbsurdity eq
extract false true eq = byBoolAbsurdity eq
extract true false eq = byBoolAbsurdity eq
extract true true eq = eq , eq

extractLeft : {P Q : Bool}
             → P and Q ≡ true
             → P ≡ true
extractLeft eq = fst (extract _ _ eq)

extractRight : {P Q : Bool}
             → P and Q ≡ true
             → Q ≡ true
extractRight eq = snd (extract _ _ eq)

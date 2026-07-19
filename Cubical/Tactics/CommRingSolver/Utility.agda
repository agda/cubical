module Cubical.Tactics.CommRingSolver.Utility where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Bool
open import Cubical.Data.Empty using (⊥) renaming (rec to recEmpty)
open import Cubical.Data.Sigma

open import Cubical.Relation.Nullary.Base

private
  variable
    ℓ ℓ' : Level
byBoolAbsurdity : {Anything : Type ℓ} → false ≡ true → Anything
byBoolAbsurdity p = recEmpty (false≢true p)

byAbsurdity : {Anything : Type ℓ} → ⊥ → Anything
byAbsurdity x = recEmpty x

extractFromAnd : (P Q : Bool)
              → P and Q ≡ true
              → (P ≡ true) × (Q ≡ true)
extractFromAnd false false eq = byBoolAbsurdity eq
extractFromAnd false true eq = byBoolAbsurdity eq
extractFromAnd true false eq = byBoolAbsurdity eq
extractFromAnd true true eq = eq , eq

extractFromAndLeft : {P Q : Bool}
             → P and Q ≡ true
             → P ≡ true
extractFromAndLeft eq = fst (extractFromAnd _ _ eq)

extractFromAndRight : {P Q : Bool}
             → P and Q ≡ true
             → Q ≡ true
extractFromAndRight eq = snd (extractFromAnd _ _ eq)

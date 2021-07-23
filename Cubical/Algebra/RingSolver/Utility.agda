{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.RingSolver.Utility where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Bool
open import Cubical.Data.Empty hiding () renaming (rec to recEmpty)
open import Cubical.Data.Sigma

open import Cubical.Relation.Nullary.Base

private
  variable
    ℓ ℓ′ : Level
byAbsurdity : {Anything : Type ℓ} → false ≡ true → Anything
byAbsurdity p = recEmpty (false≢true p)

extract : (P Q : Bool)
              → P and Q ≡ true
              → (P ≡ true) × (Q ≡ true)
extract false false eq = byAbsurdity eq
extract false true eq = byAbsurdity eq
extract true false eq = byAbsurdity eq
extract true true eq = eq , eq

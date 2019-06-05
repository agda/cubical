{-# OPTIONS --cubical --safe #-}
module Cubical.Data.Maybe.Base where

open import Cubical.Core.Everything

private
  variable
    ℓ : Level
    A B : Type ℓ

data Maybe {ℓ} (A : Type ℓ) : Type ℓ where
  nothing : Maybe A
  just    : A → Maybe A

caseMaybe : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → (n j : B) → Maybe A → B
caseMaybe n _ nothing  = n
caseMaybe _ j (just _) = j

map-Maybe : (A → B) → Maybe A → Maybe B
map-Maybe _ nothing  = nothing
map-Maybe f (just x) = just (f x)

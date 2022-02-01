{-# OPTIONS --safe #-}
module Cubical.Data.Maybe.Base where

open import Cubical.Core.Everything

private
  variable
    ℓ : Level
    A B : Type ℓ

data Maybe (A : Type ℓ) : Type ℓ where
  nothing : Maybe A
  just    : A → Maybe A

caseMaybe : (n j : B) → Maybe A → B
caseMaybe n _ nothing  = n
caseMaybe _ j (just _) = j

map-Maybe : (A → B) → Maybe A → Maybe B
map-Maybe _ nothing  = nothing
map-Maybe f (just x) = just (f x)

rec : B → (A → B) → Maybe A → B
rec n j nothing = n
rec n j (just a) = j a

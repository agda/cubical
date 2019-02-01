{-# OPTIONS --cubical --safe #-}
module Cubical.Data.Sum.Sum where

open import Cubical.Core.Everything

data _⊎_ {ℓ ℓ'} (P : Set ℓ) (Q : Set ℓ') : Set (ℓ-max ℓ ℓ') where
  inl : P → P ⊎ Q
  inr : Q → P ⊎ Q

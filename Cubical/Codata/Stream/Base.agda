{-# OPTIONS --guardedness #-}
module Cubical.Codata.Stream.Base where

open import Cubical.Foundations.Prelude

record Stream (A : Type₀) : Type₀ where
  coinductive
  constructor _,_
  field
    head : A
    tail : Stream A

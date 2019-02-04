{-# OPTIONS --cubical --safe --guardedness #-}
module Cubical.Codata.Stream.Base where

open import Cubical.Core.Everything

open import Cubical.Data.Nat

record Stream (A : Set) : Set where
  coinductive
  constructor _,_
  field
    head : A
    tail : Stream A

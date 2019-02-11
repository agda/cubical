{-# OPTIONS --cubical --safe --guardedness #-}
module Cubical.Codata.Stream.Base where

open import Cubical.Core.Everything

record Stream (A : Set) : Set where
  coinductive
  constructor _,_
  field
    head : A
    tail : Stream A

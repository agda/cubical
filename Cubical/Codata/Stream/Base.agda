{-# OPTIONS --cubical --no-import-sorts --safe --guardedness #-}
module Cubical.Codata.Stream.Base where

open import Cubical.Core.Everything

record Stream (A : Type₀) : Type₀ where
  coinductive
  constructor _,_
  field
    head : A
    tail : Stream A

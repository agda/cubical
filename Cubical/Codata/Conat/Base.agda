{-# OPTIONS --cubical --safe --guardedness #-}
module Cubical.Codata.Conat.Base where

open import Cubical.Core.Everything

data Pred (A : Set) : Set where
  pzero : Pred A
  psuc  : A → Pred A

record Conat : Set where
  coinductive
  constructor conat
  field pred : Pred Conat

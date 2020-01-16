{-# OPTIONS --cubical --safe #-}
module Cubical.Foundations.Pointed.Base where

open import Cubical.Foundations.Prelude

record Pointed ℓ : Type (ℓ-suc ℓ) where
  constructor _,_
  field
    typ : Type ℓ
    pt  : typ
open Pointed public

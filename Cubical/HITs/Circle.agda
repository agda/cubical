{- 

Definition of the circle as a HIT

-}
{-# OPTIONS --cubical #-}
module Cubical.HITs.Circle where

open import Cubical.Core.Primitives
open import Cubical.Core.Prelude

data S¹ : Set where
  base : S¹
  loop : base ≡ base

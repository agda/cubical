{-# OPTIONS --safe #-}

module Cubical.Algebra.CommRing.Instances.Bool where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.BooleanRing.Base
open import Cubical.Algebra.CommRing

open import Cubical.Algebra.BooleanRing.Instances.Bool

BoolCR : CommRing ℓ-zero
BoolCR = BooleanRing→CommRing BoolBR

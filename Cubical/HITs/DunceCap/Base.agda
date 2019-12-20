{-# OPTIONS --cubical --safe #-}

module Cubical.HITs.DunceCap.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws

open import Cubical.HITs.S1
open import Cubical.HITs.MappingCones

-- definition of the dunce cap as a mapping cone

dunceMap : S¹ → S¹
dunceMap base     = base
dunceMap (loop i) = (loop ⁻¹ ∙∙ loop ∙∙ loop) i

Dunce : Type₀
Dunce = Cone dunceMap

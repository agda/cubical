{-# OPTIONS --cubical --safe #-}
module Cubical.Data.Empty.Properties where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude

open import Cubical.Data.Empty.Base

isProp⊥ : isProp ⊥
isProp⊥ x = ⊥-elim x

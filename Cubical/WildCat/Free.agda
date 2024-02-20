-- Free wild category over a directed graph, along with (most of) its
-- universal property.
{-# OPTIONS --safe #-}

module Cubical.WildCat.Free where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path

open import Cubical.Data.Graph.Base
open import Cubical.Data.Sigma

open import Cubical.WildCat.Base
open import Cubical.WildCat.Functor
open import Cubical.WildCat.UnderlyingGraph

open WildCat
open WildFunctor

private
  variable
    ℓc ℓc' ℓd ℓd' ℓg ℓg' : Level

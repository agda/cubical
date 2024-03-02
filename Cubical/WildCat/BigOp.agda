{-
  Composition of a composable chain of morphisms in a wild category
-}
{-# OPTIONS --safe #-}

module Cubical.WildCat.BigOp where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Graph.Base
open import Cubical.Data.Graph.Path renaming (Path to GPath)

open import Cubical.WildCat.Base
open import Cubical.WildCat.Functor
open import Cubical.WildCat.UnderlyingGraph

open WildCat
open WildFunctor
open Graph

private
  variable
    ℓc ℓc' : Level

composeAll : (C : WildCat ℓc ℓc') (x y : C .ob) → (path : GPath (Cat→Graph C) x y)
             → C [ x , y ]
composeAll C x .x pnil = C .id
composeAll C x y (pcons path f) = f ∘⟨ C ⟩ composeAll C _ _ path

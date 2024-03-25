{-
  This file defines a wild category, which might be the free wild category over a
  reflexive directed graph. IT is intended to be used in a solver for wild categories
  and builds on the construction of the free wild category on a (non-reflexive) graph.
-}
{-# OPTIONS --safe #-}

module Cubical.WildCat.FreeReflexive where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Graph.Base
open import Cubical.Data.Graph.Reflexive
open import Cubical.Data.Graph.Path renaming (Path to GPath)

open import Cubical.WildCat.Base
open import Cubical.WildCat.Functor
open import Cubical.WildCat.UnderlyingGraph
import Cubical.WildCat.Free as NonReflexive


open WildCat
open WildFunctor
open Graph

private
  variable
    ℓc ℓc' ℓd ℓd' ℓg ℓg' : Level

Free : (G : RGraph ℓg ℓg') → WildCat ℓg (ℓ-max ℓg ℓg')
Free G = NonReflexive.Free (ReflGraph→Graph G)

module UniversalProperty (G : RGraph ℓg ℓg') where

  incFree : RGraphHom G (Cat→RGraph (Free G))
  incFree = ?

  {-
     G ──→ Free G
      \    ∣
   ∀ F \   ∣ ∃ F'
        ↘  ↓
          C
  -}
  inducedMorphism : (C : WildCat ℓc ℓc') → RGraphHom G (Cat→RGraph C) → WildFunctor (Free G) C
  inducedMorphism C F = {!!}

  commutes : (C : WildCat ℓc ℓc') → (F : RGraphHom G (Cat→RGraph C))
             →  incFree ⋆RGrHom (Functor→RGraphHom (inducedMorphism C F)) ≡ F
  commutes C F = {!!}

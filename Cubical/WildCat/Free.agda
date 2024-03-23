{-
  This file defines a wild category, which might be the free wild category over a
  directed graph (I do not know). This is intended to be used in a solver for
  wild categories.
-}
{-# OPTIONS --safe #-}

module Cubical.WildCat.Free where

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
    ℓc ℓc' ℓd ℓd' ℓg ℓg' : Level

Free : (G : Graph ℓg ℓg') → WildCat ℓg (ℓ-max ℓg ℓg')
ob (Free G) = G .Node
Hom[_,_] (Free G) x y = GPath G x y
id (Free G) = pnil
_⋆_ (Free G) f g = ccat G f g
⋆IdL (Free G) = pnil++ _
⋆IdR (Free G) = λ _ → refl
⋆Assoc (Free G) f g h = ++assoc G f g h


module UniversalProperty (G : Graph ℓg ℓg') where

  incFree : GraphHom G (Cat→Graph (Free G))
  incFree $g x = x
  incFree <$g> e = pcons pnil e

  {-
     G ──→ Free G
      \    ∣
   ∀ F \   ∣ ∃ F'
        ↘  ↓
          C
  -}
  ump : (C : WildCat ℓc ℓc') → GraphHom G (Cat→Graph C) → WildFunctor (Free G) C
  ump C F = F'
    where F' : WildFunctor (Free G) C
          F-ob F' = _$g_ F
          F-hom F' = {!_<$g>_!}
          F-id F' = {!!}
          F-seq F' = {!!}

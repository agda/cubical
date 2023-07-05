{-# OPTIONS --safe #-}

module Cubical.Categories.UnderlyingGraph where

open import Cubical.Categories.Morphism
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation hiding (_⟦_⟧)
open import Cubical.Data.Graph.Base
open import Cubical.Data.Sigma
open import Cubical.Categories.Isomorphism

private
  variable
    ℓc ℓc' ℓd ℓd' ℓe ℓe' ℓg ℓg' ℓh ℓh' : Level

open Category
open isIso
open Functor
open NatIso hiding (sqRL; sqLL)
open NatTrans

-- Underlying graph of a category
Ugr : ∀ {ℓc ℓc'} (𝓒 : Category ℓc ℓc') → Graph ℓc ℓc'
Ugr 𝓒 .Node = 𝓒 .ob
Ugr 𝓒 .Edge = 𝓒 .Hom[_,_]

Uhom : ∀ {ℓc ℓc' ℓd ℓd'} {𝓒 : Category ℓc ℓc'} {𝓓 : Category ℓd ℓd'} (F : Functor 𝓒 𝓓)
     → GraphHom (Ugr 𝓒) (Ugr 𝓓)
Uhom F ._$g_ = Functor.F-ob F
Uhom F ._<$g>_ = Functor.F-hom F

module _ (G : Graph ℓg ℓg') (𝓒 : Category ℓc ℓc') where
  -- Interpretation of a graph in a category
  Interp : Type _
  Interp = GraphHom G (Ugr 𝓒)
_⋆Interp_ : ∀ {G : Graph ℓg ℓg'}
              {𝓒 : Category ℓc ℓc'}
              {𝓓 : Category ℓd ℓd'}
              (ı : Interp G 𝓒)
              (F : Functor 𝓒 𝓓)
              → Interp G 𝓓
(ı ⋆Interp F) ._$g_ x = Functor.F-ob F (ı $g x)
(ı ⋆Interp F) ._<$g>_ e = Functor.F-hom F (ı <$g> e)

_∘Interp_ : ∀ {G : Graph ℓg ℓg'}
              {𝓒 : Category ℓc ℓc'}
              {𝓓 : Category ℓd ℓd'}
              (F : Functor 𝓒 𝓓)
              (ı : Interp G 𝓒)
              → Interp G 𝓓
F ∘Interp ı = ı ⋆Interp F

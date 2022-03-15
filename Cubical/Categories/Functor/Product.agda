-- Product of two functors
{-# OPTIONS --safe #-}

module Cubical.Categories.Functor.Product where

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Constructions.Product
open import Cubical.Categories.Functor.Base
open import Cubical.Data.Sigma.Properties
open import Cubical.Foundations.Prelude

private
  variable
    ℓA ℓA' ℓB ℓB' ℓC ℓC' ℓD ℓD' : Level
    A : Category ℓA ℓA'
    B : Category ℓB ℓB'
    C : Category ℓC ℓC'
    D : Category ℓD ℓD'

open Functor

_×F_ : Functor A C → Functor B D → Functor (A × B) (C × D)
(G ×F H) .F-ob (a , b) = (G ⟅ a ⟆ , H ⟅ b ⟆)
(G ×F H) .F-hom (g , h) = (G ⟪ g ⟫ , H ⟪ h ⟫)
(G ×F H) .F-id = ≡-× (G .F-id) (H .F-id)
(G ×F H) .F-seq _ _ = ≡-× (G .F-seq _ _) (H .F-seq _ _)

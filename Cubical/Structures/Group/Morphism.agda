{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Structures.Group.Morphism where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Structures.Group.Base

private
  variable
    ℓ ℓ' : Level

-- The following definition of GroupHom and GroupEquiv are level-wise heterogeneous.
-- This allows for example to deduce that G ≡ F from a chain of isomorphisms
-- G ≃ H ≃ F, even if H does not lie in the same level as G and F.

isGroupHom : (G : Group {ℓ}) (H : Group {ℓ'}) (f : ⟨ G ⟩ → ⟨ H ⟩) → Type _
isGroupHom G H f = (x y : ⟨ G ⟩) → f (x G.+ y) ≡ (f x H.+ f y) where
  module G = Group G
  module H = Group H

record GroupHom (G : Group {ℓ}) (H : Group {ℓ'}) : Type (ℓ-max ℓ ℓ') where
  constructor grouphom

  field
    fun : ⟨ G ⟩ → ⟨ H ⟩
    isHom : isGroupHom G H fun

record GroupEquiv (G : Group {ℓ}) (H : Group {ℓ'}) : Type (ℓ-max ℓ ℓ') where
  constructor groupequiv

  field
    eq : ⟨ G ⟩ ≃ ⟨ H ⟩
    isHom : isGroupHom G H (equivFun eq)

  hom : GroupHom G H
  hom = grouphom (equivFun eq) isHom

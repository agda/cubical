{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Structures.Group.Action where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Structures.Group.Base
open import Cubical.Structures.Group.Morphism
open import Cubical.Structures.LeftAction

private
  variable
    ℓ ℓ' : Level

record IsGroupAction (G : Group {ℓ = ℓ})
                     (H : Group {ℓ = ℓ'})
                     (_α_ : LeftActionStructure ⟨ G ⟩ ⟨ H ⟩) : Type (ℓ-max ℓ ℓ') where
                     
  constructor isgroupaction

  0ᴳ = Group.0g G
  _+G_ = Group._+_ G
  
  field
    isHom : (g : ⟨ G ⟩) → isGroupHom H H (g α_)
    identity : (h : ⟨ H ⟩) → 0ᴳ α h ≡ h
    assoc : (g g' : ⟨ G ⟩) → (h : ⟨ H ⟩) → ((g +G g') α h) ≡ g α (g' α h)

record GroupAction' (G : Group {ℓ = ℓ'}) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where

record GroupAction : Type (ℓ-suc (ℓ-max ℓ ℓ')) where

  constructor groupaction

  field
    G : Group {ℓ = ℓ}
    H : Group {ℓ = ℓ'}
    _α_ : LeftActionStructure ⟨ G ⟩ ⟨ H ⟩
    isGroupAction : IsGroupAction G H _α_

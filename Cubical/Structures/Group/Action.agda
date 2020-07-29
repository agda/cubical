{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Structures.Group.Action where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Structures.Group.Base
open import Cubical.Structures.Group.Morphism
open import Cubical.Structures.Group.MorphismProperties
open import Cubical.Structures.LeftAction
open import Cubical.Structures.Axioms
open import Cubical.Structures.Macro
open import Cubical.Structures.Auto
open import Cubical.Data.Sigma

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
    assoc : (g g' : ⟨ G ⟩) → (h : ⟨ H ⟩) → (g +G g') α h ≡ g α (g' α h)

record GroupAction (G : Group {ℓ}) (H : Group {ℓ'}): Type (ℓ-suc (ℓ-max ℓ ℓ')) where

  constructor groupaction

  field
    _α_ : LeftActionStructure ⟨ G ⟩ ⟨ H ⟩
    isGroupAction : IsGroupAction G H _α_

module ActionΣTheory {ℓ ℓ' : Level} where

  module _ (G : Group {ℓ}) (H : Group {ℓ'}) (_α_ : LeftActionStructure ⟨ G ⟩ ⟨ H ⟩) where
    0ᴳ = Group.0g G
    _+G_ = Group._+_ G
    IsGroupActionΣ : Type (ℓ-max ℓ ℓ')
    IsGroupActionΣ = ((g : ⟨ G ⟩) → isGroupHom H H (g α_))
                         × ((h : ⟨ H ⟩) → 0ᴳ α h ≡ h)
                         × ((g g' : ⟨ G ⟩) → (h : ⟨ H ⟩) → (g +G g') α h ≡ g α (g' α h))

    isPropIsGroupActionΣ : isProp IsGroupActionΣ
    isPropIsGroupActionΣ = isPropΣ isPropIsHom λ _ → isPropΣ isPropIdentity λ _ → isPropAssoc
      where
        isPropIsHom = isPropΠ (λ g → isPropIsGroupHom H H)
        isPropIdentity = isPropΠ (λ h → Group.is-set H (0ᴳ α h) h)
        isPropAssoc = isPropΠ3 (λ g g' h → Group.is-set H ((g +G g') α h) (g α (g' α h)))

    IsGroupAction→IsGroupActionΣ : IsGroupAction G H _α_ → IsGroupActionΣ
    IsGroupAction→IsGroupActionΣ (isgroupaction isHom identity assoc) = isHom , identity , assoc

    IsGroupActionΣ→IsGroupAction : IsGroupActionΣ → IsGroupAction G H _α_
    IsGroupActionΣ→IsGroupAction (isHom , identity , assoc) = isgroupaction isHom identity assoc

    IsGroupActionΣIso : Iso (IsGroupAction G H _α_) IsGroupActionΣ
    Iso.fun IsGroupActionΣIso = IsGroupAction→IsGroupActionΣ
    Iso.inv IsGroupActionΣIso = IsGroupActionΣ→IsGroupAction 
    Iso.rightInv IsGroupActionΣIso = λ _ → refl
    Iso.leftInv IsGroupActionΣIso = λ _ → refl

open ActionΣTheory

isPropIsGroupAction : {ℓ ℓ' : Level }
                      (G : Group {ℓ}) (H : Group {ℓ'})
                      (_α_ : LeftActionStructure ⟨ G ⟩ ⟨ H ⟩)
                      → isProp (IsGroupAction G H _α_)
isPropIsGroupAction G H _α_ = isOfHLevelRespectEquiv 1
                                                     (invEquiv (isoToEquiv (IsGroupActionΣIso G H _α_)))
                                                     (isPropIsGroupActionΣ G H _α_)


module ActionNotationα {N : Group {ℓ}} {H : Group {ℓ'}} (Act : GroupAction H N) where
  _α_ = GroupAction._α_ Act
  private
    isGroupAction = GroupAction.isGroupAction Act
  α-id = IsGroupAction.identity isGroupAction
  α-hom = IsGroupAction.isHom isGroupAction
  α-assoc = IsGroupAction.assoc isGroupAction

module ActionLemmas {G : Group {ℓ}} {H : Group {ℓ'}} (Act : GroupAction G H) where
  open ActionNotationα {N = H} {H = G} Act
  open GroupNotationH H
  open MorphismLemmas {G = H} {H = H}

  abstract
    actOnUnit : (g : ⟨ G ⟩) → g α 0ᴴ ≡ 0ᴴ
    actOnUnit g = mapId (grouphom (g α_) (α-hom g))

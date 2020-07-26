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


module Semidirect where
  open Group
  -- open IsGroup

  semidirectProduct : (N : Group {ℓ}) (H : Group {ℓ'}) (Act : GroupAction H N)
                      → Group {ℓ-max ℓ ℓ'}
  semidirectProduct N H Act
    = makeGroup-left {A = N .Carrier × H .Carrier} -- carrier
                     -- identity
                     (N .0g , H .0g)
                     -- _+_
                     (λ (n , h) (n' , h') → n +N (h α n') , h +H h')
                     -- -_
                     (λ (n , h) → (-H h) α (-N n) , -H h)
                     -- set
                     (isSetΣ (N .is-set) λ _ → H .is-set)
                     -- assoc
                     (λ (a , x) (b , y) (c , z)
                       → ΣPathP ({!_∙∙_∙∙_!} , H .assoc x y z))
                     -- lUnit
                     (λ (n , h) → ΣPathP (lUnitN ((H .0g) α n) ∙ α-id n , lUnitH h))
                     -- lCancel
                     λ (n , h) → ΣPathP ((sym (α-hom (-H h) (-N n) n) ∙∙ cong ((-H h) α_) {!lCancelN n!} ∙∙ {!!}) ,  lCancelH h)
                     where
                       _+N_ = N ._+_
                       _+H_ = H ._+_
                       -N_ = N .-_
                       -H_ = H .-_
                       lUnitH = IsGroup.lid (H .isGroup)
                       lUnitN = IsGroup.lid (N .isGroup)
                       lCancelH = IsGroup.invl (H .isGroup)
                       lCancelN = IsGroup.invl (N .isGroup)
                       open GroupAction Act
                       α-id = IsGroupAction.identity isGroupAction
                       α-hom = IsGroupAction.isHom isGroupAction

  syntax semidirectProduct N H α = N ⋊⟨ α ⟩ H

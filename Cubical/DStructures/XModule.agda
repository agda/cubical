{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.DStructures.XModule where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Functions.FunExtEquiv

open import Cubical.Homotopy.Base

open import Cubical.Data.Sigma

open import Cubical.Relation.Binary
open BinaryRelation

open import Cubical.Structures.Group
open import Cubical.Structures.LeftAction

open import Cubical.DStructures.Base
open import Cubical.DStructures.Properties
open import Cubical.DStructures.Product
open import Cubical.DStructures.Combine
open import Cubical.DStructures.Type
open import Cubical.DStructures.Group
open import Cubical.DStructures.Action

module _ (ℓ ℓ' : Level) where
  open Groups
  open Morphisms ℓ ℓ'
  open Action ℓ ℓ'

  module _ {G : Group {ℓ}} {H : Group {ℓ'}}
           (_α_ : LeftActionStructure ⟨ G ⟩ ⟨ H ⟩)
           (f : GroupHom H G) where
    f* = GroupHom.fun f
    _+G_ = Group._+_ G
    -G_  = Group.-_ G
    setG = Group.is-set G
    _+H_ = Group._+_ H
    -H_  = Group.-_ H
    setH = Group.is-set H

    isEquivariant : Type (ℓ-max ℓ ℓ')
    isEquivariant = (g : ⟨ G ⟩) → (h : ⟨ H ⟩) → f* (g α h) ≡ (g +G (f* h)) +G (-G g)

    isPropIsEquivariant : isProp isEquivariant
    isPropIsEquivariant = isPropΠ2 (λ g h → setG (f* (g α h)) ((g +G (f* h)) +G (-G g)))

    isPeiffer : Type _
    isPeiffer = (h h' : ⟨ H ⟩) → (f* h) α h' ≡ (h +H h') +H (-H h)

    isPropIsPeiffer : isProp isPeiffer
    isPropIsPeiffer = isPropΠ2 (λ h h' → setH ((f* h) α h') ((h +H h') +H (-H h)))

  G²ActB = Σ[ (((G , H) , _α_) , isAct) ∈ G²Act ] (GroupHom H G)
  G²ActBEqui = Σ[ (((GH , _α_) , isAct ) , f) ∈ G²ActB ] (isEquivariant _α_ f)
  PreXModuleΣ = G²ActBEqui
  G²ActBEquiPeif = Σ[ ((((GH , _α_) , isAct) , f) , isEqui) ∈ G²ActBEqui ] (isPeiffer _α_ f)
  XModuleΣ = G²ActBEquiPeif

  -- displayed over SAction, a morphism back
  SᴰPreXModuleStr : URGStrᴰ SAction
                           (λ (((G , H) , _) , _) → GroupHom H G)
                           (ℓ-max ℓ ℓ')
  SᴰPreXModuleStr = make-𝒮ᴰ (λ {(((G , H) , _α_) , isAct) } {_α'_} f (((eG , eH) , eLas) , eIsAct) f'
                                   → let trEG = GroupEquiv.eq eG .fst
                                         trEH = GroupEquiv.eq eH .fst
                                         f* = GroupHom.fun f
                                         f'* = GroupHom.fun f'
                                     in (h : ⟨ H ⟩) → trEG (f* h) ≡ f'* (trEH h))
                                (λ _ _ → refl)
                                λ (((G , H) , _α_) , isAct) f
                                  → isOfHLevelRespectEquiv 0
                                                           (Σ-cong-equiv-snd (λ f' → isoToEquiv (invIso (GroupMorphismExtIso f f'))))
                                                           (isContrSingl f)

  SPreXModuleStr : URGStr G²ActB (ℓ-max ℓ ℓ')
  SPreXModuleStr = ∫⟨ SAction ⟩ SᴰPreXModuleStr


  -- add equivariance condition
  SᴰPreXModule : URGStrᴰ SPreXModuleStr
                         (λ (((GH , _α_) , isAct) , f) → isEquivariant _α_ f)
                         ℓ-zero
  SᴰPreXModule = Subtype→Sub-𝒮ᴰ (λ (((GH , _α_) , isAct) , f)
                                    → isEquivariant _α_ f , isPropIsEquivariant _α_ f)
                                 SPreXModuleStr

  SPreXModule : URGStr G²ActBEqui (ℓ-max ℓ ℓ')
  SPreXModule = ∫⟨ SPreXModuleStr ⟩ SᴰPreXModule

  SᴰXModule : URGStrᴰ SPreXModule
                      (λ (((((G , H) , _α_) , isAct) , f) , isEqui)
                        → isPeiffer _α_ f)
                      ℓ-zero
  SᴰXModule = Subtype→Sub-𝒮ᴰ (λ (((((G , H) , _α_) , isAct) , f) , isEqui)
                                 → isPeiffer _α_ f , isPropIsPeiffer _α_ f)
                              SPreXModule

  SXModule : URGStr G²ActBEquiPeif (ℓ-max ℓ ℓ')
  SXModule = ∫⟨ SPreXModule ⟩ SᴰXModule

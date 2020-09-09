{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.DStructures.Structures.XModule where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Functions.FunExtEquiv

open import Cubical.Homotopy.Base

open import Cubical.Data.Sigma

open import Cubical.Relation.Binary


open import Cubical.Algebra.Group
open import Cubical.Structures.LeftAction

open import Cubical.DStructures.Base
open import Cubical.DStructures.Meta.Properties
open import Cubical.DStructures.Structures.Constant
open import Cubical.DStructures.Meta.Combine
open import Cubical.DStructures.Structures.Type
open import Cubical.DStructures.Structures.Group
open import Cubical.DStructures.Structures.Action

private
  variable
    ℓ ℓ' : Level

-------------------------------------------------
-- Definitions and properties of
-- equivariance and peiffer condition
-------------------------------------------------
module _ ((((G₀ , H) , _α_) , isAct) : Action ℓ ℓ') (φ : GroupHom H G₀) where

  open GroupNotation₀ G₀
  open GroupNotationᴴ H

  private
    f = GroupHom.fun φ

  -- α is equivariant w.r.t φ if φ (g α h) ≡ g + (φ h) - g
  isEquivariant : Type (ℓ-max ℓ ℓ')
  isEquivariant = (g : ⟨ G₀ ⟩) → (h : ⟨ H ⟩) → f (g α h) ≡ (g +₀ f h) -₀ g

  -- G₀ is a set, so isEquivariant is a proposition
  isPropIsEquivariant : isProp isEquivariant
  isPropIsEquivariant = isPropΠ2 (λ g h → set₀ (f (g α h)) ((g +₀ f h) -₀ g))

  -- (α, φ) satisfies the peiffer condition, if
  -- (φ h) α h' ≡ h + h' - h
  isPeiffer : Type ℓ'
  isPeiffer = (h h' : ⟨ H ⟩) → (f h) α h' ≡ (h +ᴴ h') -ᴴ h

  -- H is a set, so isPeiffer is a proposition
  isPropIsPeiffer : isProp isPeiffer
  isPropIsPeiffer = isPropΠ2 (λ h h' → setᴴ ((f h) α h') ((h +ᴴ h') -ᴴ h))

module _ (ℓ ℓ' : Level) where
  ----------------------
  -- Define the types of
  -- - Actions α with a morphism φ
  -- - Precrossed modules
  -- - Crossed modules
  -- and add URG structures to them
  ----------------------
  ActionB = Σ[ (((G₀ , H) , _α_) , isAct) ∈ Action ℓ ℓ' ] (GroupHom H G₀)
  PreXModule = Σ[ (α , φ) ∈ ActionB ] (isEquivariant α φ)
  XModule = Σ[ ((α , φ) , isEqui) ∈ PreXModule ] (isPeiffer α φ)

  -- displayed over 𝒮-Action, a morphism back
  -- by lifting the morphism back over Grp² twice
  𝒮ᴰ-Action\PreXModuleStr : URGStrᴰ (𝒮-Action ℓ ℓ')
                           (λ (((G , H) , _) , _) → GroupHom H G)
                           (ℓ-max ℓ ℓ')
  𝒮ᴰ-Action\PreXModuleStr = VerticalLift2-𝒮ᴰ (𝒮-group ℓ ×𝒮 𝒮-group ℓ')
                                               (𝒮ᴰ-G²\B ℓ ℓ')
                                               (𝒮ᴰ-G²\Las ℓ ℓ')
                                               (𝒮ᴰ-G²Las\Action ℓ ℓ')

  𝒮-PreXModuleStr : URGStr ActionB (ℓ-max ℓ ℓ')
  𝒮-PreXModuleStr = ∫⟨ 𝒮-Action ℓ ℓ' ⟩ 𝒮ᴰ-Action\PreXModuleStr


  -- add equivariance condition
  -- use that equivariance is a proposition
  𝒮ᴰ-PreXModule : URGStrᴰ 𝒮-PreXModuleStr
                         (λ (α , φ) → isEquivariant α φ)
                         ℓ-zero
  𝒮ᴰ-PreXModule = Subtype→Sub-𝒮ᴰ (λ (α , φ) → isEquivariant α φ , isPropIsEquivariant α φ)
                                 𝒮-PreXModuleStr

  𝒮-PreXModule : URGStr PreXModule (ℓ-max ℓ ℓ')
  𝒮-PreXModule = ∫⟨ 𝒮-PreXModuleStr ⟩ 𝒮ᴰ-PreXModule

  -- add the proposition isPeiffer to precrossed modules
  𝒮ᴰ-XModule : URGStrᴰ 𝒮-PreXModule
                       (λ ((α , φ) , isEqui) → isPeiffer α φ)
                       ℓ-zero
  𝒮ᴰ-XModule = Subtype→Sub-𝒮ᴰ (λ ((α , φ) , isEqui) → isPeiffer α φ , isPropIsPeiffer α φ)
                              𝒮-PreXModule

  𝒮-XModule : URGStr XModule (ℓ-max ℓ ℓ')
  𝒮-XModule = ∫⟨ 𝒮-PreXModule ⟩ 𝒮ᴰ-XModule


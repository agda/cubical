
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.DStructures.Strict2Group where

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


module _ (ℓ ℓ' : Level) where
  open Groups
  open Morphisms ℓ ℓ'

  -- displayed over pairs of groups, one morphism going forth and two going back
  GroupsMorphismFBBᴰ : URGStrᴰ (URGStrGroup ℓ ×URG URGStrGroup ℓ')
                               (λ (G , H) → (GroupHom G H × GroupHom H G) × GroupHom H G)
                               (ℓ-max ℓ ℓ')
  GroupsMorphismFBBᴰ = combineURGStrᴰ GroupsMorphismFBᴰ GroupsMorphismBᴰ

  -- type of pairs of groups with one morphism going forth and two going back
  GroupsMorphismFBB : URGStr (Σ[ (G , H) ∈ Group × Group ] (GroupHom G H × GroupHom H G) × GroupHom H G) (ℓ-max ℓ ℓ')
  GroupsMorphismFBB = ∫⟨ URGStrGroup ℓ ×URG URGStrGroup ℓ' ⟩ GroupsMorphismFBBᴰ

  GroupsMorphismSecRetBᴰ : URGStrᴰ GroupsMorphismFBB (λ ((G , H) , (f , b) , b') → isGroupHomRet f b) (ℓ-max ℓ ℓ')
  GroupsMorphismSecRetBᴰ = HorizontalLiftᴰ GroupsMorphismFBᴰ GroupsMorphismBᴰ GroupsSecRetᴰ

{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.DStructures.Structures.Strict2Group where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Functions.FunExtEquiv

open import Cubical.Homotopy.Base

open import Cubical.Data.Sigma

open import Cubical.Relation.Binary


open import Cubical.Structures.Group
open import Cubical.Structures.LeftAction

open import Cubical.DStructures.Base
open import Cubical.DStructures.Meta.Properties
open import Cubical.DStructures.Meta.Combine
open import Cubical.DStructures.Structures.Constant
open import Cubical.DStructures.Structures.Type
open import Cubical.DStructures.Structures.Group
open import Cubical.DStructures.Structures.ReflGraph
open import Cubical.DStructures.Structures.VertComp

module _ (ℓ ℓ' : Level) where
  private
    ℓℓ' = ℓ-max ℓ ℓ'


  𝒮ᴰ-Strict2Group : URGStrᴰ (𝒮-ReflGraph ℓ ℓ')
                            VertComp
                            ℓ-zero
  𝒮ᴰ-Strict2Group = Subtype→Sub-𝒮ᴰ (λ 𝒢 → VertComp 𝒢 , isPropVertComp 𝒢)
                                   (𝒮-ReflGraph ℓ ℓ')

  Strict2Group : Type (ℓ-suc ℓℓ')
  Strict2Group = Σ[ 𝒢 ∈ ReflGraph ℓ ℓ' ] VertComp 𝒢

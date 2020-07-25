{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.DStructures.Isomorphism where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

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

private
  variable
    ℓ ℓ' ℓ'' ℓ₁ ℓ₁' ℓ₁'' ℓ₂ ℓA ℓA' ℓ≅A ℓ≅A' ℓB ℓB' ℓ≅B ℓC ℓ≅C ℓ≅ᴰ ℓ≅ᴰ' : Level

module _ {A : Type ℓA} (𝒮-A : URGStr A ℓ≅A)
         {A' : Type ℓA'} (𝒮-A' : URGStr A' ℓ≅A') where

       𝒮-iso : Type (ℓ-max (ℓ-max ℓA ℓA') (ℓ-max ℓ≅A ℓ≅A'))
       𝒮-iso = RelIso (URGStr._≅_ 𝒮-A) (URGStr._≅_ 𝒮-A')

       𝒮-iso→Iso : 𝒮-iso → Iso A A'
       𝒮-iso→Iso f = RelIso→Iso (_≅_ 𝒮-A) (_≅_ 𝒮-A') (ρ 𝒮-A) (ρ 𝒮-A') (uni 𝒮-A) (uni 𝒮-A') f
         where
           open URGStr

{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.DStructures.Experiments where

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

private
  variable
    ℓ ℓ' : Level

module _ (ℓ ℓ' : Level) where
  open Groups
  open Morphisms ℓ ℓ'

  S-Group = URGStrGroup
  Sᴰ-G²\F = SᴰG²F
  Sᴰ-G²\SecRet = SᴰG²SecRet

  Sᴰ-G\GF : URGStrᴰ (URGStrGroup ℓ)
                    (λ G → Σ[ H ∈ Group {ℓ'} ] GroupHom G H)
                    (ℓ-max ℓ ℓ')
  Sᴰ-G\GF = splitTotalURGStrᴰ (URGStrGroup ℓ)
                               (URGStrConstᴰ (URGStrGroup ℓ)
                                             (URGStrGroup ℓ'))
                               Sᴰ-G²\F



{-
  Sᴰ-G\GSecRet : URGStrᴰ (URGStrGroup ℓ)
                         {!!}
                         {!!}
  Sᴰ-G\GSecRet = splitTotalURGStrᴰ (URGStrGroup ℓ)
                                   {!!}
                                   {!!}
-}

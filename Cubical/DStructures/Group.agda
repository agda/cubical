{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.DStructures.Group where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Path
open import Cubical.Foundations.SIP
open import Cubical.Data.Sigma

open import Cubical.DStructures.DispSIP
open import Cubical.Relation.Binary
open BinaryRelation
open import Cubical.Structures.Group


module _ (ℓ : Level) where
  URGStrGroup : URGStr (Group {ℓ = ℓ}) ℓ
  URGStrGroup = urgstr GroupEquiv
                       idGroupEquiv
                       (isUnivalent'→isUnivalent GroupEquiv
                                                 idGroupEquiv
                                                 λ G H → invEquiv (GroupPath G H))


module _ (ℓ ℓ' : Level) where
  URGStrAction : URGStrᴰ (URGStrGroup ℓ)
                         (λ G → Σ[ H ∈ Group {ℓ = ℓ'} ] GroupHom G H)
                         {!ℓ-max ℓ ℓ'!}

  URGStrAction = {!!}

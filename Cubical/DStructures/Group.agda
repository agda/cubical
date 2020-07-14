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

private
  variable
    ℓ ℓ' ℓ'' ℓ₁ ℓ₁' ℓ₁'' ℓ₂ ℓA ℓ≅A ℓB ℓ≅B ℓ≅ᴰ : Level

URGStrGroup : URGStr (Group {ℓ = ℓ}) ℓ
-- URGStrGroup = makeURGStr {_≅_ = GroupEquiv} idGroupEquiv {!!}
URGStrGroup = urgstr GroupEquiv idGroupEquiv
  (λ G H → record { equiv-proof = λ e → {!!} })

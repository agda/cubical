{-# OPTIONS --cubical --safe #-}

module Cubical.Relation.Binary.Properties where

open import Cubical.Relation.Binary.Base
open import Cubical.HITs.SetQuotients.Base
open import Cubical.HITs.SetQuotients.Properties
open import Cubical.Core.Prelude
open import Cubical.Core.Glue
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv

open BinaryRelation



module BinaryRelationProperties {ℓ ℓ' : Level} {A : Set ℓ} (R : A → A → hProp {ℓ = ℓ'}) where


{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.DStructures.Structures.Higher where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Functions.FunExtEquiv

open import Cubical.Homotopy.Base

open import Cubical.Data.Sigma
open import Cubical.Data.Nat

open import Cubical.Relation.Binary

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Higher

open import Cubical.DStructures.Base
open import Cubical.DStructures.Meta.Properties
open import Cubical.DStructures.Structures.Constant
open import Cubical.DStructures.Meta.Combine
open import Cubical.DStructures.Structures.Type

private
  variable
    ℓ ℓ' ℓA ℓ≅A : Level

{-
module _ (ℓ : Level) where
  𝒮-BGroup : (n k : ℕ) → URGStr (BGroup ℓ n k) ℓ
  𝒮-BGroup n k =
    make-𝒮 {_≅_ = λ BG BH → {!!}}
           {!!}
           {!!}
-}

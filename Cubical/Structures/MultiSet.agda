{-# OPTIONS --cubical --no-import-sorts --no-exact-split --safe #-}
module Cubical.Structures.MultiSet where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.SIP renaming (SNS-PathP to SNS)
open import Cubical.Functions.FunExtEquiv

open import Cubical.Structures.Auto

open import Cubical.Data.Nat
open import Cubical.Data.Sigma

private
  variable
    ℓ : Level

module _ (A : Type ℓ) (Aset : isSet A) where

 count-structure : Type ℓ → Type ℓ
 count-structure X = A → X → ℕ

 count-iso : StrIso count-structure _
 count-iso = autoIso count-structure

 count-is-SNS : SNS _ count-iso
 count-is-SNS = autoSNS count-structure

 Count : Type (ℓ-suc ℓ)
 Count = TypeWithStr ℓ count-structure

 multi-set-structure : Type ℓ → Type ℓ
 multi-set-structure X = X × (A → X → X) × (A → X → ℕ)

 multi-set-iso : StrIso multi-set-structure _
 multi-set-iso = autoIso multi-set-structure

 Multi-Set-is-SNS : SNS _ multi-set-iso
 Multi-Set-is-SNS = autoSNS multi-set-structure

 Multi-Set : Type (ℓ-suc ℓ)
 Multi-Set = TypeWithStr ℓ multi-set-structure

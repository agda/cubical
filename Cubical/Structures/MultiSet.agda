{-# OPTIONS --cubical --no-import-sorts --no-exact-split --safe #-}
module Cubical.Structures.MultiSet where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.SIP renaming (SNS-PathP to SNS)
open import Cubical.Functions.FunExtEquiv

open import Cubical.Structures.Macro
open import Cubical.Structures.LeftAction

open import Cubical.Data.Unit
open import Cubical.Data.Sum
open import Cubical.Data.Nat
open import Cubical.Data.Sigma

private
  variable
    ℓ : Level

module _(A : Type ℓ)
        (Aset : isSet A) where

 count-desc = param A (recvar (constant ℕ))

 open Macro ℓ count-desc public renaming
   ( structure to count-structure
   ; iso to count-iso
   ; isSNS to Count-is-SNS
   )

 Count : Type (ℓ-suc ℓ)
 Count = TypeWithStr ℓ count-structure

 open Macro ℓ (var , (param A (recvar var)) , count-desc) public renaming
   ( structure to multi-set-structure
   ; iso to multi-set-iso
   ; isSNS to Multi-Set-is-SNS
   )

 Multi-Set : Type (ℓ-suc ℓ)
 Multi-Set = TypeWithStr ℓ multi-set-structure

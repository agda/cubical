{-# OPTIONS --no-exact-split --safe #-}
module Cubical.Structures.MultiSet where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.SIP
open import Cubical.Functions.FunExtEquiv

open import Cubical.Structures.Auto

open import Cubical.Data.Nat
open import Cubical.Data.Sigma

private
  variable
    ℓ : Level

module _ (A : Type ℓ) (Aset : isSet A) where

 CountStructure : Type ℓ → Type ℓ
 CountStructure X = A → X → ℕ

 CountEquivStr = AutoEquivStr CountStructure

 countUnivalentStr : UnivalentStr _ CountEquivStr
 countUnivalentStr = autoUnivalentStr CountStructure

 Count : Type (ℓ-suc ℓ)
 Count = TypeWithStr ℓ CountStructure

 MultiSetStructure : Type ℓ → Type ℓ
 MultiSetStructure X = X × (A → X → X) × (A → X → ℕ)

 MultiSetEquivStr = AutoEquivStr MultiSetStructure

 multiSetUnivalentStr : UnivalentStr _ MultiSetEquivStr
 multiSetUnivalentStr = autoUnivalentStr MultiSetStructure

 MultiSet : Type (ℓ-suc ℓ)
 MultiSet = TypeWithStr ℓ MultiSetStructure

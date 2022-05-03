{-# OPTIONS --safe #-}
module Cubical.Algebra.Group.Instances.DiffInt where

open import Cubical.HITs.SetQuotients
open import Cubical.Foundations.Prelude
open import Cubical.Data.Int.MoreInts.DiffInt renaming (ℤ to ℤType ; _+_ to _+ℤ_ ; _-_ to _-ℤ_)
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Semigroup.Base
open import Cubical.Algebra.Monoid.Base

open GroupStr

ℤ-isGroup : IsGroup {G = ℤType} ([ 0 , 0 ]) (_+ℤ_) (-ℤ_)
IsSemigroup.is-set (IsMonoid.isSemigroup (IsGroup.isMonoid ℤ-isGroup)) = ℤ-isSet
IsSemigroup.assoc (IsMonoid.isSemigroup (IsGroup.isMonoid ℤ-isGroup)) = +ℤ-assoc
IsMonoid.identity (IsGroup.isMonoid ℤ-isGroup) = λ x → (zero-identityʳ 0 x  , zero-identityˡ 0 x)
IsGroup.inverse ℤ-isGroup = λ x → (-ℤ-invʳ x , -ℤ-invˡ x)

ℤ : Group₀
fst ℤ = ℤType
1g (snd ℤ) = [ 0 , 0 ]
_·_ (snd ℤ) = _+ℤ_
inv (snd ℤ) = -ℤ_
isGroup (snd ℤ) = ℤ-isGroup

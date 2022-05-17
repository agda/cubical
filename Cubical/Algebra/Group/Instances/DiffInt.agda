{-# OPTIONS --safe #-}
module Cubical.Algebra.Group.Instances.DiffInt where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Int.MoreInts.DiffInt renaming ( _+_ to _+ℤ_ ; _-_ to _-ℤ_)

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Semigroup.Base
open import Cubical.Algebra.Monoid.Base

open import Cubical.HITs.SetQuotients

open GroupStr


ℤ-isGroup : IsGroup {G = ℤ} ([ 0 , 0 ]) (_+ℤ_) (-ℤ_)
IsSemigroup.is-set (IsMonoid.isSemigroup (IsGroup.isMonoid ℤ-isGroup)) = ℤ-isSet
IsSemigroup.assoc (IsMonoid.isSemigroup (IsGroup.isMonoid ℤ-isGroup)) = +ℤ-assoc
IsMonoid.identity (IsGroup.isMonoid ℤ-isGroup) = λ x → (zero-identityʳ 0 x  , zero-identityˡ 0 x)
IsGroup.inverse ℤ-isGroup = λ x → (-ℤ-invʳ x , -ℤ-invˡ x)

ℤGroup : Group₀
fst ℤGroup = ℤ
1g (snd ℤGroup) = [ 0 , 0 ]
_·_ (snd ℤGroup) = _+ℤ_
inv (snd ℤGroup) = -ℤ_
isGroup (snd ℤGroup) = ℤ-isGroup

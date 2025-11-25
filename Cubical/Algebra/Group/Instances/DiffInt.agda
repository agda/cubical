module Cubical.Algebra.Group.Instances.DiffInt where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Int.MoreInts.DiffInt renaming ( _+_ to _+ℤ_ ; _-_ to _-ℤ_)

open import Cubical.Algebra.Group.Base

open import Cubical.HITs.SetQuotients

open GroupStr

ℤGroup : Group₀
fst ℤGroup = ℤ
1g (snd ℤGroup) = [ 0 , 0 ]
_·_ (snd ℤGroup) = _+ℤ_
inv (snd ℤGroup) = -ℤ_
isGroup (snd ℤGroup) = makeIsGroup
                       ℤ-isSet
                       +ℤ-assoc
                       (λ x → zero-identityʳ 0 x)
                       (λ x → zero-identityˡ 0 x)
                       -ℤ-invʳ
                       -ℤ-invˡ

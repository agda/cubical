{-# OPTIONS --safe #-}
module Cubical.Algebra.Group.Instances.Int where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Int
  renaming (_+_ to _+ℤ_ ; _-_ to _-ℤ_; -_ to -ℤ_ ; _·_ to _·ℤ_)

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Properties
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties


open GroupStr

ℤGroup : Group₀
fst ℤGroup = ℤ
1g (snd ℤGroup) = 0
_·_ (snd ℤGroup) = _+ℤ_
inv (snd ℤGroup) = -ℤ_
isGroup (snd ℤGroup) = isGroupℤ
  where
  abstract
    isGroupℤ : IsGroup (pos 0) (_+ℤ_) (-ℤ_)
    isGroupℤ = makeIsGroup isSetℤ
                           +Assoc (λ _ → refl) (+Comm 0)
                           -Cancel -Cancel'

ℤHom : (n : ℤ) → GroupHom ℤGroup ℤGroup
fst (ℤHom n) x = n ·ℤ x
snd (ℤHom n) =
  makeIsGroupHom λ x y → ·DistR+ n x y

negEquivℤ : GroupEquiv ℤGroup ℤGroup
fst negEquivℤ =
  isoToEquiv
    (iso (GroupStr.inv (snd ℤGroup))
         (GroupStr.inv (snd ℤGroup))
         (GroupTheory.invInv ℤGroup)
         (GroupTheory.invInv ℤGroup))
snd negEquivℤ =
  makeIsGroupHom -Dist+

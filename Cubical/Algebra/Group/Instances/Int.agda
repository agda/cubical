{-# OPTIONS --safe #-}
module Cubical.Algebra.Group.Instances.Int where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Int
  renaming (ℤ to ℤType ; _+_ to _+ℤ_ ; _-_ to _-ℤ_; -_ to -ℤ_ ; _·_ to _·ℤ_)
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Properties

open GroupStr

ℤ : Group₀
fst ℤ = ℤType
1g (snd ℤ) = 0
_·_ (snd ℤ) = _+ℤ_
inv (snd ℤ) = -ℤ_
isGroup (snd ℤ) = isGroupℤ
  where
  abstract
    isGroupℤ : IsGroup (pos 0) (_+ℤ_) (-ℤ_)
    isGroupℤ = makeIsGroup isSetℤ
                           +Assoc (λ _ → refl) (+Comm 0)
                           -Cancel -Cancel'

ℤHom : (n : ℤType) → GroupHom ℤ ℤ
fst (ℤHom n) x = n ·ℤ x
snd (ℤHom n) =
  makeIsGroupHom λ x y → ·DistR+ n x y

negEquivℤ : GroupEquiv ℤ ℤ
fst negEquivℤ =
  isoToEquiv
    (iso (GroupStr.inv (snd ℤ))
         (GroupStr.inv (snd ℤ))
         (GroupTheory.invInv ℤ)
         (GroupTheory.invInv ℤ))
snd negEquivℤ =
  makeIsGroupHom -Dist+

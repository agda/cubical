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
inv (snd ℤ) = _-ℤ_ 0
isGroup (snd ℤ) = isGroupℤ
  where
  abstract
    isGroupℤ : IsGroup (pos 0) _+ℤ_ (_-ℤ_ (pos 0))
    isGroupℤ = makeIsGroup isSetℤ +Assoc (λ _ → refl) (+Comm 0)
                           (λ x → +Comm x (pos 0 -ℤ x) ∙ minusPlus x 0)
                           (λ x → minusPlus x 0)

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
  makeIsGroupHom λ x y
    → +Comm (pos 0) (-ℤ (x +ℤ y))
    ∙ -Dist+ x y
    ∙ cong₂ _+ℤ_ (+Comm (-ℤ x) (pos 0)) (+Comm (-ℤ y) (pos 0))

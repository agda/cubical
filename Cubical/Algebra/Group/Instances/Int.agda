{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.Group.Instances.Int where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Int renaming (_+_ to _+Int_ ; _-_ to _-Int_; -_ to -Int_)
open import Cubical.Algebra.Group.Base

open GroupStr

intGroup : Group₀
fst intGroup = Int
0g (snd intGroup) = 0
_+_ (snd intGroup) = _+Int_
- snd intGroup = _-Int_ 0
isGroup (snd intGroup) = isGroupInt
  where
  abstract
    isGroupInt : IsGroup (pos 0) _+Int_ (_-Int_ (pos 0))
    isGroupInt = makeIsGroup isSetInt +-assoc (λ x → refl) (λ x → +-comm 0 x)
                              (λ x → +-comm x (pos 0 -Int x) ∙ minusPlus x 0) (λ x → minusPlus x 0)

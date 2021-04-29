{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.Group.Instances.Int where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Int renaming (Int to IntType ; _+_ to _+Int_ ; _-_ to _-Int_; -_ to -Int_ ; _·_ to _·Int_)
open import Cubical.Algebra.Group.Base

open GroupStr

Int : Group₀
fst Int = IntType
1g (snd Int) = 0
_·_ (snd Int) = _+Int_
inv (snd Int) = _-Int_ 0
isGroup (snd Int) = isGroupInt
  where
  abstract
    isGroupInt : IsGroup (pos 0) _+Int_ (_-Int_ (pos 0))
    isGroupInt = makeIsGroup isSetInt +-assoc (λ x → refl) (λ x → +-comm 0 x)
                              (λ x → +-comm x (pos 0 -Int x) ∙ minusPlus x 0) (λ x → minusPlus x 0)

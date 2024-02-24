{-# OPTIONS --safe #-}
module Cubical.WildCat.Product where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma renaming (_×_ to _×'_)

open import Cubical.WildCat.Base

private
  variable
    ℓ ℓ' : Level
    ℓC ℓC' ℓD ℓD' : Level

open WildCat

_×_ :  (C : WildCat ℓC ℓC') (D : WildCat ℓD ℓD') → WildCat _ _
ob (C × D) = ob C ×' ob D
Hom[_,_] (C × D) (c , d) (c' , d') =
  Hom[_,_] C c c' ×' Hom[_,_] D d d'
id (C × D) = id C , id D
_⋆_ (C × D) f g = _⋆_ C (fst f) (fst g) , _⋆_ D (snd f) (snd g)
⋆IdL (C × D) (f , g) i = (⋆IdL C f i) , (⋆IdL D g i)
⋆IdR (C × D) (f , g) i = (⋆IdR C f i) , (⋆IdR D g i)
⋆Assoc (C × D) (f , g) (f' , g') (f'' , g'') i =
  ⋆Assoc C f f' f'' i , ⋆Assoc D g g' g'' i

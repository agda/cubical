{-# OPTIONS --safe #-}
module Cubical.WildCat.Instances.Path where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws

open import Cubical.WildCat.Base

private
  variable
    ℓ : Level

open WildCat

PathCat : (A : Type ℓ) → WildCat ℓ ℓ
ob (PathCat A) = A
Hom[_,_] (PathCat A) x y = (x ≡ y)
id (PathCat A) = refl
_⋆_ (PathCat A) = _∙_
⋆IdL (PathCat A) p = sym (lUnit p)
⋆IdR (PathCat A) p = sym (rUnit p)
⋆Assoc (PathCat A) p q r = sym (assoc p q r)

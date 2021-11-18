-- Discrete category over a type
{-# OPTIONS --safe #-}

module Cubical.Categories.Instances.Discrete where

open import Cubical.Categories.Category.Base using (Precategory)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Foundations.GroupoidLaws using (lUnit; rUnit; assoc)
open import Cubical.Foundations.Prelude using (Level; Type; ℓ-zero; _≡_; refl; _∙_; sym)

private
  variable
    ℓ : Level

open Precategory

Discrete : Type ℓ → Precategory ℓ ℓ
Discrete A .ob = A
Discrete A .Hom[_,_] a a' = a ≡ a'
Discrete A .id a = refl
Discrete A ._⋆_ = _∙_
Discrete A .⋆IdL f = sym (lUnit f)
Discrete A .⋆IdR f = sym (rUnit f)
Discrete A .⋆Assoc f g h = sym (assoc f g h)
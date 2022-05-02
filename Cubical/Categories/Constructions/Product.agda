-- Product of type-many categories
{-# OPTIONS --safe #-}

module Cubical.Categories.Constructions.Product where

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude

private
  variable
    ℓA ℓC ℓC' : Level

open Category

ΠC : (A : Type ℓA) → (catC : A → Category ℓC ℓC') → Category (ℓ-max ℓA ℓC) (ℓ-max ℓA ℓC')
ob (ΠC A catC) = (a : A) → ob (catC a)
Hom[_,_] (ΠC A catC) c c' = (a : A) → catC a [ c a , c' a ]
id (ΠC A catC) a = id (catC a)
_⋆_ (ΠC A catC) g f a = g a ⋆⟨ catC a ⟩ f a
⋆IdL (ΠC A catC) f = funExt λ a → ⋆IdL (catC a) (f a)
⋆IdR (ΠC A catC) f = funExt λ a → ⋆IdR (catC a) (f a)
⋆Assoc (ΠC A catC) h g f = funExt λ a → ⋆Assoc (catC a) (h a) (g a) (f a)
isSetHom (ΠC A catC) = isSetΠ (λ a → isSetHom (catC a))

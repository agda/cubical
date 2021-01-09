{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Categories.Instances.Cospan where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Data.Unit
open import Cubical.Data.Empty

open Precategory

data 𝟛 : Type ℓ-zero where
  ⓪ : 𝟛
  ① : 𝟛
  ② : 𝟛

Cospan : Precategory ℓ-zero ℓ-zero
Cospan .ob = 𝟛

Cospan .Hom[_,_] ⓪ ① = Unit
Cospan .Hom[_,_] ② ① = Unit
Cospan .Hom[_,_] ⓪ ⓪ = Unit
Cospan .Hom[_,_] ① ① = Unit
Cospan .Hom[_,_] ② ② = Unit
Cospan .Hom[_,_] _ _ = ⊥


Cospan ._⋆_ {x = ⓪} {⓪} {⓪} f g = tt
Cospan ._⋆_ {x = ①} {①} {①} f g = tt
Cospan ._⋆_ {x = ②} {②} {②} f g = tt
Cospan ._⋆_ {x = ⓪} {①} {①} f g = tt
Cospan ._⋆_ {x = ②} {①} {①} f g = tt
Cospan ._⋆_ {x = ⓪} {⓪} {①} f g = tt
Cospan ._⋆_ {x = ②} {②} {①} f g = tt

Cospan .id ⓪ = tt
Cospan .id ① = tt
Cospan .id ② = tt

Cospan .⋆IdL {⓪} {①} _ = refl
Cospan .⋆IdL {②} {①} _ = refl
Cospan .⋆IdL {⓪} {⓪} _ = refl
Cospan .⋆IdL {①} {①} _ = refl
Cospan .⋆IdL {②} {②} _ = refl

Cospan .⋆IdR {⓪} {①} _ = refl
Cospan .⋆IdR {②} {①} _ = refl
Cospan .⋆IdR {⓪} {⓪} _ = refl
Cospan .⋆IdR {①} {①} _ = refl
Cospan .⋆IdR {②} {②} _ = refl

Cospan .⋆Assoc {⓪} {⓪} {⓪} {⓪} _ _ _ = refl
Cospan .⋆Assoc {⓪} {⓪} {⓪} {①} _ _ _ = refl
Cospan .⋆Assoc {⓪} {⓪} {①} {①} _ _ _ = refl
Cospan .⋆Assoc {⓪} {①} {①} {①} _ _ _ = refl
Cospan .⋆Assoc {①} {①} {①} {①} _ _ _ = refl
Cospan .⋆Assoc {②} {②} {②} {②} _ _ _ = refl
Cospan .⋆Assoc {②} {②} {②} {①} _ _ _ = refl
Cospan .⋆Assoc {②} {②} {①} {①} _ _ _ = refl
Cospan .⋆Assoc {②} {①} {①} {①} _ _ _ = refl

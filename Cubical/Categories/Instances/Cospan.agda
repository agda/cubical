{-# OPTIONS --safe #-}
module Cubical.Categories.Instances.Cospan where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Data.Unit
open import Cubical.Data.Empty

open Category

data 𝟛 : Type ℓ-zero where
  ⓪ : 𝟛
  ① : 𝟛
  ② : 𝟛

CospanCat : Category ℓ-zero ℓ-zero
CospanCat .ob = 𝟛

CospanCat .Hom[_,_] ⓪ ① = Unit
CospanCat .Hom[_,_] ② ① = Unit
CospanCat .Hom[_,_] ⓪ ⓪ = Unit
CospanCat .Hom[_,_] ① ① = Unit
CospanCat .Hom[_,_] ② ② = Unit
CospanCat .Hom[_,_] _ _ = ⊥

CospanCat ._⋆_ {x = ⓪} {⓪} {⓪} f g = tt
CospanCat ._⋆_ {x = ①} {①} {①} f g = tt
CospanCat ._⋆_ {x = ②} {②} {②} f g = tt
CospanCat ._⋆_ {x = ⓪} {①} {①} f g = tt
CospanCat ._⋆_ {x = ②} {①} {①} f g = tt
CospanCat ._⋆_ {x = ⓪} {⓪} {①} f g = tt
CospanCat ._⋆_ {x = ②} {②} {①} f g = tt

CospanCat .id {⓪} = tt
CospanCat .id {①} = tt
CospanCat .id {②} = tt

CospanCat .⋆IdL {⓪} {①} _ = refl
CospanCat .⋆IdL {②} {①} _ = refl
CospanCat .⋆IdL {⓪} {⓪} _ = refl
CospanCat .⋆IdL {①} {①} _ = refl
CospanCat .⋆IdL {②} {②} _ = refl

CospanCat .⋆IdR {⓪} {①} _ = refl
CospanCat .⋆IdR {②} {①} _ = refl
CospanCat .⋆IdR {⓪} {⓪} _ = refl
CospanCat .⋆IdR {①} {①} _ = refl
CospanCat .⋆IdR {②} {②} _ = refl

CospanCat .⋆Assoc {⓪} {⓪} {⓪} {⓪} _ _ _ = refl
CospanCat .⋆Assoc {⓪} {⓪} {⓪} {①} _ _ _ = refl
CospanCat .⋆Assoc {⓪} {⓪} {①} {①} _ _ _ = refl
CospanCat .⋆Assoc {⓪} {①} {①} {①} _ _ _ = refl
CospanCat .⋆Assoc {①} {①} {①} {①} _ _ _ = refl
CospanCat .⋆Assoc {②} {②} {②} {②} _ _ _ = refl
CospanCat .⋆Assoc {②} {②} {②} {①} _ _ _ = refl
CospanCat .⋆Assoc {②} {②} {①} {①} _ _ _ = refl
CospanCat .⋆Assoc {②} {①} {①} {①} _ _ _ = refl

CospanCat .isSetHom {⓪} {⓪} = isSetUnit
CospanCat .isSetHom {⓪} {①} = isSetUnit
CospanCat .isSetHom {①} {①} = isSetUnit
CospanCat .isSetHom {②} {①} = isSetUnit
CospanCat .isSetHom {②} {②} = isSetUnit


-- makes it easier to write functors into CospanCat
isPropHomCospanCat : (x y : ob CospanCat) → isProp (CospanCat [ x , y ])
isPropHomCospanCat ⓪ ⓪ = isPropUnit
isPropHomCospanCat ⓪ ① = isPropUnit
isPropHomCospanCat ⓪ ② = isProp⊥
isPropHomCospanCat ① ⓪ = isProp⊥
isPropHomCospanCat ① ① = isPropUnit
isPropHomCospanCat ① ② = isProp⊥
isPropHomCospanCat ② ⓪ = isProp⊥
isPropHomCospanCat ② ① = isPropUnit
isPropHomCospanCat ② ② = isPropUnit

{-# OPTIONS --safe #-}
module Cubical.WildCat.Instances.Types where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed hiding (⋆ ; id)
open import Cubical.Foundations.Function using (idfun) renaming (_∘_ to _∘fun_)

open import Cubical.WildCat.Base

open WildCat

TypeCat : (ℓ : Level) → WildCat (ℓ-suc ℓ) ℓ
ob (TypeCat ℓ) = Type ℓ
Hom[_,_] (TypeCat ℓ) A B = A → B
WildCat.id (TypeCat ℓ) = idfun _
_⋆_ (TypeCat ℓ) f g = g ∘fun f
⋆IdL (TypeCat ℓ) = λ _ → refl
⋆IdR (TypeCat ℓ) = λ _ → refl
⋆Assoc (TypeCat ℓ) f g h = refl

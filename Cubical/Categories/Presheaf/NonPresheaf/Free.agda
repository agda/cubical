{-# OPTIONS --safe #-}
module Cubical.Categories.Presheaf.NonPresheaf.Free where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Constructions.Product
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation

open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.NonPresheaf.Forget

open Category
open Functor
open NatTrans

private
  variable
    ℓ ℓ' ℓS : Level

freePresheaf : (C : Category ℓ ℓ') → NonPresheaf C ℓS → Presheaf C {!!}
fst (F-ob (freePresheaf C X) c) = Σ[ d ∈ ob C ] C [ c , d ] × fst (X d)
snd (F-ob (freePresheaf C X) c) = {!isSetΣ!}
F-hom (freePresheaf C X) = {!!}
F-id (freePresheaf C X) = {!!}
F-seq (freePresheaf C X) = {!!}

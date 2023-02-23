{-# OPTIONS --safe #-}
module Cubical.Categories.Presheaf.NonPresheaf.Forget where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Categories.Category
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Constructions.Product
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation

open import Cubical.Categories.Presheaf.Base

open Category
open Functor
open NatTrans

private
  variable
    ℓ ℓ' ℓS : Level

NonPresheaf : Category ℓ ℓ' → (ℓS : Level) → Type (ℓ-max ℓ (ℓ-suc ℓS))
NonPresheaf C ℓS = ob C → hSet ℓS

NonPresheafCategory : Category ℓ ℓ' → (ℓS : Level)
          → Category (ℓ-max ℓ (ℓ-suc ℓS)) (ℓ-max ℓ ℓS)
NonPresheafCategory C ℓS = ΠC (ob C) (λ _ → SET ℓS)

ForgetPresheaf : (C : Category ℓ ℓ') → Functor (PresheafCategory C ℓS) (NonPresheafCategory C ℓS)
F-ob (ForgetPresheaf C) pshX = F-ob pshX
F-hom (ForgetPresheaf C) {pshX} {pshY} pshF = N-ob pshF
F-id (ForgetPresheaf C) {pshX} = refl
F-seq (ForgetPresheaf C) {pshX} {pshY} {pshZ} pshF pshG = refl

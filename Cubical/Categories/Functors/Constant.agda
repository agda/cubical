{-# OPTIONS --safe #-}

module Cubical.Categories.Functors.Constant where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Functor.Base

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

open Category
open Functor

Constant : (C : Category ℓC ℓC') (D : Category ℓD ℓD') (d : ob D) → Functor C D
F-ob (Constant C D d) c = d
F-hom (Constant C D d) φ = id D
F-id (Constant C D d) = refl
F-seq (Constant C D d) φ χ = sym (⋆IdR D _)

ConstantComposeFunctor :
  (C : Category ℓC ℓC') (D : Category ℓD ℓD' ) (c : C .ob)
  (F : Functor C D) →
  Constant (D ^op) D (F .F-ob c) ≡ F ∘F Constant (D ^op) C c
ConstantComposeFunctor C D c F = Functor≡
  (λ c → ( refl ))
    (λ f → (
      D .id
     ≡⟨ sym (F .F-id) ⟩
       F ⟪ Constant (D ^op) C c ⟪ f ⟫ ⟫ ∎
  ))

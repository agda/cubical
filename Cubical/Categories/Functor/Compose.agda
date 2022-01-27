{-# OPTIONS --safe #-}

module Cubical.Categories.Functor.Compose where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation.Base

open import Cubical.Categories.Instances.Functors

module _ {ℓC ℓC' ℓD ℓD' ℓE ℓE'}
  {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} (E : Category ℓE ℓE')
  (F : Functor C D)
  where

  open Functor
  open NatTrans

  precomposeF : Functor (FUNCTOR D E) (FUNCTOR C E)
  precomposeF .F-ob G = funcComp G F
  precomposeF .F-hom α .N-ob c = α .N-ob (F .F-ob c)
  precomposeF .F-hom α .N-hom f = α .N-hom (F .F-hom f)
  precomposeF .F-id = refl
  precomposeF .F-seq f g = refl

module _ {ℓC ℓC' ℓD ℓD' ℓE ℓE'}
  (C : Category ℓC ℓC') {D : Category ℓD ℓD'} {E : Category ℓE ℓE'}
  (G : Functor D E)
  where

  open Functor
  open NatTrans

  postcomposeF : Functor (FUNCTOR C D) (FUNCTOR C E)
  postcomposeF .F-ob F = funcComp G F
  postcomposeF .F-hom α .N-ob c = G. F-hom (α .N-ob c)
  postcomposeF .F-hom {F₀} {F₁} α .N-hom {x} {y} f =
    sym (G .F-seq (F₀ ⟪ f ⟫) (α ⟦ y ⟧))
    ∙∙ cong (G ⟪_⟫) (α .N-hom f)
    ∙∙ G .F-seq (α ⟦ x ⟧) (F₁ ⟪ f ⟫)
  postcomposeF .F-id = makeNatTransPath (funExt λ _ → G .F-id)
  postcomposeF .F-seq f g = makeNatTransPath (funExt λ _ → G .F-seq _ _)

{-# OPTIONS --safe #-}

module Cubical.Categories.Dagger.Functor where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor

open import Cubical.Categories.Dagger.Base
open import Cubical.Categories.Dagger.Properties

private variable
  ℓC ℓC' ℓD ℓD' : Level

record DagFunctor (C : DagCat ℓC ℓC') (D : DagCat ℓD ℓD') : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where
  no-eta-equality

  open Category
  open DagCat

  field
    F-cat : Functor (C .cat) (D .cat)
    F-† : ∀ {x y} (f : C .cat [ x , y ]) → F-cat ⟪ f †[ C ] ⟫ ≡ F-cat ⟪ f ⟫ †[ D ]

  isEssentially†Surj = (d : D .ob) → ∃[ c ∈ C .ob ] †CatIso D (F-cat ⟅ c ⟆) d

  open Functor F-cat public

open DagFunctor
open Functor

private variable
  ℓ ℓ' ℓ'' ℓ''' : Level
  B C D E : DagCat ℓ ℓ'

Id†Func : DagFunctor C C
Id†Func .F-cat = Id
Id†Func .F-† f = refl

Comp†Func : DagFunctor C D → DagFunctor D E → DagFunctor C E
Comp†Func F G .F-cat = G .F-cat ∘F F .F-cat
Comp†Func {C = C} {D = D} {E = E} F G .F-† f =
  G .F-cat ⟪ F .F-cat ⟪ f †[ C ] ⟫ ⟫ ≡⟨ cong (G .F-hom) (F .F-† f) ⟩
  G .F-cat ⟪ F .F-cat ⟪ f ⟫ †[ D ] ⟫ ≡⟨ G .F-† (F .F-hom f) ⟩
  G .F-cat ⟪ F .F-cat ⟪ f ⟫ ⟫ †[ E ] ∎

†Func^op : DagFunctor C D → DagFunctor (opDagCat C) (opDagCat D)
†Func^op F .F-cat = F .F-cat ^opF
†Func^op F .F-† f = F .F-† f

†Func≡ : ∀ (F G : DagFunctor C D) → F .F-cat ≡ G .F-cat → F ≡ G
†Func≡ {C = C} {D = D} F G p i .F-cat = p i
†Func≡ {C = C} {D = D} F G p i .F-† f = isProp→PathP {B = λ i → p i ⟪ f †[ C ] ⟫ ≡ p i ⟪ f ⟫ †[ D ]}
  (λ _ → D .DagCat.isSetHom _ _) (F .F-† f) (G .F-† f) i


{-# OPTIONS --hidden-argument-puns #-}

module Cubical.Categories.Dagger.Functor where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Functors.Constant

open import Cubical.Categories.Dagger.Base

private variable
  ℓC ℓC' ℓD ℓD' ℓ ℓ' ℓ'' ℓ''' : Level
  C D E : †Category ℓ ℓ'

open †Category

module _ (C : †Category ℓC ℓC') (D : †Category ℓD ℓD') where
  record Is†Functor (F : Functor (C .cat) (D .cat)) : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where
    no-eta-equality
    field
      F-† : ∀ {x y} (f : C .cat [ x , y ]) → F ⟪ f †[ C ] ⟫ ≡ F ⟪ f ⟫ †[ D ]

  open Is†Functor public

  isPropIs†Functor : ∀ F → isProp (Is†Functor F)
  isPropIs†Functor F a b i .F-† f = D .isSetHom _ _ (a .F-† f) (b .F-† f) i

  †Functor : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD'))
  †Functor = Σ[ F ∈ Functor (C .cat) (D .cat) ] Is†Functor F

open Functor

†Id : †Functor C C
†Id .fst = Id
†Id .snd .F-† f = refl

†FuncComp : †Functor C D → †Functor D E → †Functor C E
†FuncComp F G .fst = G .fst ∘F F .fst
†FuncComp {C} {D} {E} F G .snd .F-† f =
  G .fst ⟪ F .fst ⟪ f †[ C ] ⟫ ⟫ ≡⟨ cong (G .fst .F-hom) (F .snd .F-† f) ⟩
  G .fst ⟪ F .fst ⟪ f ⟫ †[ D ] ⟫ ≡⟨ G .snd .F-† (F .fst .F-hom f) ⟩
  G .fst ⟪ F .fst ⟪ f ⟫ ⟫ †[ E ] ∎

_∘†F_ : †Functor D E → †Functor C D → †Functor C E
G ∘†F F = †FuncComp F G

†Func≡ : (F G : †Functor C D) → F .fst ≡ G .fst → F ≡ G
†Func≡ {C} {D} F G = Σ≡Prop (isPropIs†Functor C D)

open †Category

†Constant : ob D → †Functor C D
†Constant {D} d .fst = Constant _ _ d
†Constant {D} d .snd .F-† _ = sym (D .†-id)

open NatTrans

NT† : (F G : †Functor C D) → NatTrans (F .fst) (G .fst) → NatTrans (G .fst) (F .fst)
NT† {C} {D} F G n .N-ob x = n ⟦ x ⟧ †[ D ]
NT† {C} {D} F G n .N-hom {x} {y} f =
  G .fst ⟪ f ⟫ D.⋆ n ⟦ y ⟧ D.†         ≡⟨ congL D._⋆_ (sym (D .†-invol (G .fst ⟪ f ⟫))) ⟩
  G .fst ⟪ f ⟫ D.† D.† D.⋆ n ⟦ y ⟧ D.† ≡⟨ sym (D .†-seq (n ⟦ y ⟧) (G .fst ⟪ f ⟫ D.†)) ⟩
  (n ⟦ y ⟧ D.⋆ G .fst ⟪ f ⟫ D.†) D.†   ≡⟨ cong D._† (congR D._⋆_ (sym (G .snd .F-† f))) ⟩
  (n ⟦ y ⟧ D.⋆ G .fst ⟪ f C.† ⟫) D.†   ≡⟨ cong D._† (sym (n .N-hom (f C.†))) ⟩
  (F .fst ⟪ f C.† ⟫ D.⋆ n ⟦ x ⟧) D.†   ≡⟨ cong D._† (congL D._⋆_ (F .snd .F-† f)) ⟩
  (F .fst ⟪ f ⟫ D.† D.⋆ n ⟦ x ⟧) D.†   ≡⟨ D .†-seq (F .fst ⟪ f ⟫ D.†) (n ⟦ x ⟧) ⟩
  n ⟦ x ⟧ D.† D.⋆ F .fst ⟪ f ⟫ D.† D.† ≡⟨ congR D._⋆_ (D .†-invol (F .fst ⟪ f ⟫)) ⟩
  n ⟦ x ⟧ D.† D.⋆ F .fst ⟪ f ⟫         ∎
  where module D = †Category D; module C = †Category C

{-# OPTIONS --safe #-}

module Cubical.Categories.Adjoint.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Adjoint
open import Cubical.Categories.Instances.Functors

open Iso

open Functor
open NatTrans
open Category
open NaturalBijection
open _⊣_


{-
Adjunctions with a parameter

Theorem IV.7.3 of Categories for the Working Mathematician by Saunders Mac Lane

Given a bifunctor F : C → [D , E] and for each c ∈ C that F ⟅ c ⟆ has a right adjoint,
this data fills out a bifunctor G : (C ^op) → [E , D]
-}
module _ {ℓC ℓC' ℓD ℓD' ℓE ℓE' : Level} {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} {E : Category ℓE ℓE'}
         (F : Functor C (FUNCTOR D E)) (G : (c : C .ob) → isLeftAdjoint (F ⟅ c ⟆)) where

  private
    module _ (x y : C .ob) (f : C [ x , y ]) where
      φ'⁻¹ : ∀ {d e} → D [ d , G y .fst ⟅ e ⟆ ] → E [ (F ⟅ y ⟆) ⟅ d ⟆ , e ]
      φ'⁻¹ = G y .snd ♯

      φ : ∀ {d e} → E [ (F ⟅ x ⟆) ⟅ d ⟆ , e ] → D [ d , G x .fst ⟅ e ⟆ ]
      φ = G x .snd ♭

      σ* : ∀ {d e} → E [ (F ⟅ y ⟆) ⟅ d ⟆ , e ] → E [ (F ⟅ x ⟆) ⟅ d ⟆ , e ]
      σ* {d} {e} k = F ⟪ f ⟫ ⟦ d ⟧ ⋆⟨ E ⟩ k

      τ* : ∀ {d e} → D [ d , G y .fst ⟅ e ⟆ ] → D [ d , G x .fst ⟅ e ⟆ ]
      τ* f = φ (σ* (φ'⁻¹ f))

      -- using Yoneda Lemma to produce the unique family of arrows that is a natural transformation
      -- conjugate to F ⟪ f ⟫
      τ : G y .fst ⇒ G x .fst
      τ .N-ob x = τ* (D .id)
      τ .N-hom {x₁} {y₁} g =
        G y .fst ⟪ g ⟫ ⋆⟨ D ⟩ (G x .snd ♭) (F ⟪ f ⟫ ⟦ G y .fst ⟅ y₁ ⟆ ⟧ ⋆⟨ E ⟩ (G y .snd ♯) (D .id))
          ≡⟨ adjNatInC' (G x .snd) ((F ⟪ f ⟫ ⟦ G y .fst ⟅ y₁ ⟆ ⟧ ⋆⟨ E ⟩ (G y .snd ♯) (D .id))) (G y .fst ⟪ g ⟫)  ⟩
        (G x .snd ♭) ((F ⟅ x ⟆) ⟪ G y .fst ⟪ g ⟫ ⟫ ⋆⟨ E ⟩ ((F ⟪ f ⟫) ⟦ G y .fst ⟅ y₁ ⟆ ⟧ ⋆⟨ E ⟩ (G y .snd ♯) (D .id)))
          ≡[ i ]⟨ (G x .snd ♭) (E .⋆Assoc ((F ⟅ x ⟆) ⟪ G y .fst ⟪ g ⟫ ⟫) ((F ⟪ f ⟫) ⟦ G y .fst ⟅ y₁ ⟆ ⟧) ((G y .snd ♯) (D .id)) (~ i)) ⟩
        (G x .snd ♭) ((F ⟅ x ⟆) ⟪ G y .fst ⟪ g ⟫ ⟫ ⋆⟨ E ⟩ (F ⟪ f ⟫) ⟦ G y .fst ⟅ y₁ ⟆ ⟧ ⋆⟨ E ⟩ (G y .snd ♯) (D .id))
          ≡[ i ]⟨ (G x .snd ♭) ((F ⟪ f ⟫) .N-hom (G y .fst ⟪ g ⟫) i ⋆⟨ E ⟩ (G y .snd ♯) (D .id)) ⟩
        (G x .snd ♭) ((F ⟪ f ⟫) ⟦ G y .fst ⟅ x₁ ⟆ ⟧ ⋆⟨ E ⟩ (F ⟅ y ⟆) ⟪ G y .fst ⟪ g ⟫ ⟫ ⋆⟨ E ⟩ (G y .snd ♯) (D .id))
          ≡[ i ]⟨ (G x .snd ♭) (E .⋆Assoc ((F ⟪ f ⟫) ⟦ G y .fst ⟅ x₁ ⟆ ⟧) ((F ⟅ y ⟆) ⟪ G y .fst ⟪ g ⟫ ⟫) ((G y .snd ♯) (D .id)) i) ⟩
        (G x .snd ♭) ((F ⟪ f ⟫) ⟦ G y .fst ⟅ x₁ ⟆ ⟧ ⋆⟨ E ⟩ ((F ⟅ y ⟆) ⟪ G y .fst ⟪ g ⟫ ⟫ ⋆⟨ E ⟩ (G y .snd ♯) (D .id)))
          ≡[ i ]⟨ (G x .snd ♭) ((F ⟪ f ⟫) ⟦ G y .fst ⟅ x₁ ⟆ ⟧ ⋆⟨ E ⟩ (adjNatInC (G y .snd) (D .id) (G y .fst ⟪ g ⟫) (~ i))) ⟩
        (G x .snd ♭) ((F ⟪ f ⟫) ⟦ G y .fst ⟅ x₁ ⟆ ⟧ ⋆⟨ E ⟩ (G y .snd ♯) ((G y .fst ⟪ g ⟫) ⋆⟨ D ⟩ D .id))
          ≡[ i ]⟨ (G x .snd ♭) ((F ⟪ f ⟫) ⟦ G y .fst ⟅ x₁ ⟆ ⟧ ⋆⟨ E ⟩ (G y .snd ♯) (D .⋆IdR (G y .fst ⟪ g ⟫) i)) ⟩
        (G x .snd ♭) (F ⟪ f ⟫ ⟦ G y .fst ⟅ x₁ ⟆ ⟧ ⋆⟨ E ⟩ (G y .snd ♯) ((G y .fst) ⟪ g ⟫))
          ≡[ i ]⟨ (G x .snd ♭) ((F ⟪ f ⟫) ⟦ G y .fst ⟅ x₁ ⟆ ⟧ ⋆⟨ E ⟩ (G y .snd ♯) (D .⋆IdL (G y .fst ⟪ g ⟫) (~ i))) ⟩
        (G x .snd ♭) (F ⟪ f ⟫ ⟦ G y .fst ⟅ x₁ ⟆ ⟧ ⋆⟨ E ⟩ (G y .snd ♯) (D .id ⋆⟨ D ⟩ ((G y .fst) ⟪ g ⟫)))
          ≡[ i ]⟨ (G x .snd ♭) (F ⟪ f ⟫ ⟦ G y .fst ⟅ x₁ ⟆ ⟧ ⋆⟨ E ⟩ adjNatInD' (G y .snd) (D .id) g (~ i)) ⟩
        (G x .snd ♭) (F ⟪ f ⟫ ⟦ G y .fst ⟅ x₁ ⟆ ⟧ ⋆⟨ E ⟩ ((G y .snd ♯) (D .id) ⋆⟨ E ⟩ g))
          ≡⟨ G x .snd .adjNatInD (F ⟪ f ⟫ ⟦ G y .fst ⟅ x₁ ⟆ ⟧) ((G y .snd ♯) (D .id) ⋆⟨ E ⟩ g) ⟩
        (G x .snd ♭) (F ⟪ f ⟫ ⟦ G y .fst ⟅ x₁ ⟆ ⟧) ⋆⟨ D ⟩ (G x .fst) ⟪ (G y .snd ♯) (D .id) ⋆⟨ E ⟩ g ⟫
          ≡[ i ]⟨ (G x .snd ♭) (F ⟪ f ⟫ ⟦ G y .fst ⟅ x₁ ⟆ ⟧) ⋆⟨ D ⟩ (G x .fst .F-seq ((G y .snd ♯) (D .id)) g i) ⟩
        (G x .snd ♭) (F ⟪ f ⟫ ⟦ G y .fst ⟅ x₁ ⟆ ⟧) ⋆⟨ D ⟩ ((G x .fst) ⟪ (G y .snd ♯) (D .id) ⟫ ⋆⟨ D ⟩ G x .fst ⟪ g ⟫)
          ≡⟨ sym (D .⋆Assoc ((G x .snd ♭) (F ⟪ f ⟫ ⟦ G y .fst ⟅ x₁ ⟆ ⟧)) ((G x .fst) ⟪ (G y .snd ♯) (D .id) ⟫) (G x .fst ⟪ g ⟫)) ⟩
        (G x .snd ♭) (F ⟪ f ⟫ ⟦ G y .fst ⟅ x₁ ⟆ ⟧) ⋆⟨ D ⟩ (G x .fst) ⟪ (G y .snd ♯) (D .id) ⟫ ⋆⟨ D ⟩ G x .fst ⟪ g ⟫
          ≡[ i ]⟨ G x .snd .adjNatInD (F ⟪ f ⟫ ⟦ G y .fst ⟅ x₁ ⟆ ⟧) ((G y .snd ♯) (D .id)) (~ i) ⋆⟨ D ⟩ G x .fst ⟪ g ⟫  ⟩
        (G x .snd ♭) (F ⟪ f ⟫ ⟦ G y .fst ⟅ x₁ ⟆ ⟧ ⋆⟨ E ⟩ (G y .snd ♯) (D .id)) ⋆⟨ D ⟩ G x .fst ⟪ g ⟫
          ∎

  fillsOut-Bifunctor : Functor (C ^op) (FUNCTOR E D)
  fillsOut-Bifunctor .F-ob c = G c .fst
  fillsOut-Bifunctor .F-hom {x} {y} f = τ y x f
  fillsOut-Bifunctor .F-id {x} = makeNatTransPath (funExt λ e →
    (G x .snd ♭) (F ⟪ C .id ⟫ ⟦ (G x .fst) ⟅ e ⟆ ⟧ ⋆⟨ E ⟩ (G x .snd ♯) (D .id))
      ≡[ i ]⟨ (G x .snd ♭) (F .F-id i ⟦ (G x .fst) ⟅ e ⟆ ⟧ ⋆⟨ E ⟩ (G x .snd ♯) (D .id)) ⟩
    (G x .snd ♭) (E .id ⋆⟨ E ⟩ (G x .snd ♯) (D .id))
      ≡[ i ]⟨ (G x .snd ♭) (E .⋆IdL ((G x .snd ♯) (D .id)) i) ⟩
    (G x .snd ♭) ((G x .snd ♯) (D .id))
      ≡⟨ G x .snd .adjIso .rightInv (D .id) ⟩
    D .id
      ∎)
  fillsOut-Bifunctor .F-seq {x} {y} {z} f g = makeNatTransPath (funExt λ e →
    cong (λ a → (G z .snd ♭) a)
         ((λ i → F .F-seq g f i ⟦ G x .fst ⟅ e ⟆ ⟧ ⋆⟨ E ⟩ (G x .snd ♯) (D .id))
          ∙ E .⋆Assoc ((F ⟪ g ⟫) ⟦ G x .fst ⟅ e ⟆ ⟧) ((F ⟪ f ⟫) ⟦ G x .fst ⟅ e ⟆ ⟧) ((G x .snd ♯) (D .id))
          ∙ cong (λ a → (F ⟪ g ⟫) ⟦ G x .fst ⟅ e ⟆ ⟧ ⋆⟨ E ⟩ a)
                 (sym (G y .snd .adjIso .leftInv ((F ⟪ f ⟫) ⟦ G x .fst ⟅ e ⟆ ⟧ ⋆⟨ E ⟩ (G x .snd ♯) (D .id)))
                 ∙ (λ i → (G y .snd ♯) (D .⋆IdR ((G y .snd ♭) ((F ⟪ f ⟫) ⟦ G x .fst ⟅ e ⟆ ⟧ ⋆⟨ E ⟩ (G x .snd ♯) (D .id))) (~ i)))
                 ∙ adjNatInC (G y .snd)
                             (D .id)
                             ((G y .snd ♭) (seq' E ((F ⟪ f ⟫) ⟦ G x .fst ⟅ e ⟆ ⟧) ((G x .snd ♯) (D .id)))))
          ∙ sym (E .⋆Assoc ((F ⟪ g ⟫) ⟦ G x .fst ⟅ e ⟆ ⟧)
                           ((F ⟅ y ⟆) ⟪
                             (G y .snd ♭) (
                               (F ⟪ f ⟫) ⟦ G x .fst ⟅ e ⟆ ⟧
                                 ⋆⟨ E ⟩
                               (G x .snd ♯) (D .id))⟫)
                           ((G y .snd ♯) (D .id)))
          ∙ (λ i → (F ⟪ g ⟫) .N-hom ((G y .snd ♭) (seq' E ((F ⟪ f ⟫) ⟦ G x .fst ⟅ e ⟆ ⟧) ((G x .snd ♯) (D .id)))) (~ i)
                     ⋆⟨ E ⟩
                   (G y .snd ♯) (D .id))
          ∙ E .⋆Assoc ((F ⟅ z ⟆) ⟪
                        (G y .snd ♭) ((F ⟪ f ⟫) ⟦ G x .fst ⟅ e ⟆ ⟧ ⋆⟨ E ⟩ (G x .snd ♯) (D .id))⟫)
                      ((F ⟪ g ⟫) ⟦ G y .fst ⟅ e ⟆ ⟧)
                      ((G y .snd ♯) (D .id)))
    ∙ sym (adjNatInC' (G z .snd)
                      ((F ⟪ g ⟫) ⟦ G y .fst ⟅ e ⟆ ⟧ ⋆⟨ E ⟩ (G y .snd ♯) (D .id))
                      ((G y .snd ♭) ((F ⟪ f ⟫) ⟦ G x .fst ⟅ e ⟆ ⟧ ⋆⟨ E ⟩ (G x .snd ♯) (D .id)))))

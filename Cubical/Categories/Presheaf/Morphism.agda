{-# OPTIONS --safe #-}
module Cubical.Categories.Presheaf.Morphism where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.Elements
open import Cubical.Categories.Constructions.Lift
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Limits
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Data.Sigma

{-

  Given two presheaves P and Q on the same category C, a morphism
  between them is a natural transformation. Here we generalize this to
  situations where P and Q are presheaves on *different* categories.

  Given a functor F : C → D, a presheaf P on C and a presheaf Q on D,
  we can define a homomorphism from P to Q over F as a natural
  transformation from P to Q o F^op. (if we had implicit cumulativity)

  These are the homs of a 2-category of presheaves displayed over the
  2-category of categories.

-}
private
  variable
    ℓc ℓc' ℓd ℓd' ℓp ℓq : Level

open Category
open Contravariant
open Functor
open NatTrans
open UnivElt
open isUniversal

module _ {C : Category ℓc ℓc'}{D : Category ℓd ℓd'} (F : Functor C D) (P : Presheaf C ℓp) (Q : Presheaf D ℓq) where
  PshHom : Type (ℓ-max (ℓ-max (ℓ-max ℓc ℓc') ℓp) ℓq)
  PshHom = PresheafCategory C (ℓ-max ℓp ℓq) [ LiftF {ℓp}{ℓq} ∘F P , LiftF {ℓq}{ℓp} ∘F Q ∘F (F ^opF) ]

  module _ (h : PshHom) where
    -- This should define a functor on the category of elements
    push-elt : Elementᴾ {C = C} P → Elementᴾ {C = D} Q
    push-elt (A , η) = (F ⟅ A ⟆) , (h .N-ob A (lift η) .lower)

    push-eltNat : ∀ {B : C .ob} (η : Elementᴾ {C = C} P) (f : C [ B , η .fst ])
                  → D [ push-elt η .snd ∘ᴾ⟨ Q ⟩ F .F-hom f ]
                    ≡ push-elt (B , C [ η .snd ∘ᴾ⟨ P ⟩ f ]) .snd
    push-eltNat η f i = h .N-hom f (~ i) (lift (η .snd)) .lower

    push-eltF : Functor (∫ᴾ_ {C = C} P) (∫ᴾ_ {C = D} Q)
    push-eltF .F-ob = push-elt
    push-eltF .F-hom {x}{y} (f , commutes) = F .F-hom f , sym (
      D [ push-elt _ .snd ∘ᴾ⟨ Q ⟩ F .F-hom f ]
        ≡⟨ push-eltNat y f ⟩
      push-elt (_ , C [ y .snd ∘ᴾ⟨ P ⟩ f ]) .snd
        ≡⟨ cong (λ a → push-elt a .snd) (ΣPathP (refl , (sym commutes))) ⟩
      push-elt x .snd ∎)
    push-eltF .F-id = Σ≡Prop (λ x → (Q ⟅ _ ⟆) .snd _ _) (F .F-id)
    push-eltF .F-seq f g = Σ≡Prop ((λ x → (Q ⟅ _ ⟆) .snd _ _)) (F .F-seq (f .fst) (g .fst))

    preserves-representation : ∀ (η : UnivElt C P) → Type (ℓ-max (ℓ-max ℓd ℓd') ℓq)
    preserves-representation η = isUniversal D Q (push-elt (elementᴾ _ _ η))

    preserves-representability : Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓc ℓc') ℓd) ℓd') ℓp) ℓq)
    preserves-representability = ∀ η → preserves-representation η

    -- What is the nice HoTT formulation of this?
    preserve-represention→preserves-representability :
      ∀ η → preserves-representation η → preserves-representability
    preserve-represention→preserves-representability η preserves-η η' =
      isTerminalElement→isUniversal D Q
        (preserveOnePreservesAll (∫ᴾ_ {C = C} P)
                                 (∫ᴾ_ {C = D} Q)
                                 push-eltF
                                 (UnivElt→UniversalElement C P η)
                                 (isUniversal→isTerminalElement D Q preserves-η)
                                 (UnivElt→UniversalElement C P η'))

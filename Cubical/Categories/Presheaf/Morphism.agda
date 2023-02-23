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

{-

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

    preserves-representation : ∀ (η : UnivElt C P) → Type (ℓ-max (ℓ-max ℓd ℓd') ℓq)
    preserves-representation η = isUniversal D Q (push-elt (elementᴾ _ _ η))

    preserves-representability : Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓc ℓc') ℓd) ℓd') ℓp) ℓq)
    preserves-representability = ∀ η → preserves-representation η

    -- What is the nice HoTT formulation of this?
    -- Probably would have been easier to use terminal objects in ∫ᴾ here...
    preserve-represention→preserves-representability :
      ∀ η → preserves-representation η → preserves-representability
    preserve-represention→preserves-representability η preserves-η η' .coinduction ϕ =
      F .F-hom (univEltIso _ _ (η .universal) (η' .universal) .fst) ∘⟨ D ⟩ preserves-η .coinduction ϕ
    preserve-represention→preserves-representability η preserves-η η' .commutes ϕ =
      (D [ push-elt (elementᴾ C P η') .snd
           ∘ᴾ⟨ Q ⟩ F .F-hom (η' .universal .coinduction (η .element))
           ∘⟨ D ⟩ preserves-η .coinduction ϕ ])
        ≡⟨ ∘ᴾAssoc D Q _ _ _ ⟩
      (D [ D [ push-elt (elementᴾ C P η') .snd
               ∘ᴾ⟨ Q ⟩ F .F-hom (η' .universal .coinduction (η .element)) ]
               ∘ᴾ⟨ Q ⟩ preserves-η .coinduction ϕ ])
        ≡[ i ]⟨ D [ push-eltNat (elementᴾ C P η') ((η' .universal .coinduction (η .element))) i ∘ᴾ⟨ Q ⟩ preserves-η .coinduction ϕ ] ⟩
      (D [ push-elt ((η .vertex) , (C [ η' .element ∘ᴾ⟨ P ⟩ η' .universal .coinduction (η .element) ])) .snd
           ∘ᴾ⟨ Q ⟩ preserves-η .coinduction ϕ ])
        ≡[ i ]⟨ D [ push-elt ((η .vertex) , (η' .universal .commutes (η .element) i)) .snd ∘ᴾ⟨ Q ⟩ preserves-η .coinduction ϕ ]  ⟩
      (D [ push-elt (η .vertex , η .element) .snd ∘ᴾ⟨ Q ⟩ preserves-η .coinduction ϕ ])
        ≡⟨ preserves-η .commutes ϕ ⟩
      ϕ ∎
    preserve-represention→preserves-representability η preserves-η η' .is-uniq ϕ f f-commutes =
      ⋆InvRMove (F-Iso {C = C}{D = D}{F = F} (univEltIso C P (η' .universal) (η .universal)))
                (preserves-η .is-uniq ϕ (F .F-hom (η .universal .coinduction (η' .element)) ∘⟨ D ⟩ f)
                (D [ push-elt (elementᴾ _ _ η) .snd ∘ᴾ⟨ Q ⟩ (F .F-hom (η .universal .coinduction (η' .element)) ∘⟨ D ⟩ f) ]
                  ≡⟨ ∘ᴾAssoc D Q (push-elt (elementᴾ _ _ η) .snd) (F .F-hom (η .universal .coinduction (η' .element))) f ⟩
                 D [ D [ push-elt (elementᴾ _ _ η) .snd
                         ∘ᴾ⟨ Q ⟩ (F .F-hom (η .universal .coinduction (η' .element))) ]
                         ∘ᴾ⟨ Q ⟩ f  ]
                  ≡[ i ]⟨ D [ push-eltNat (elementᴾ _ _ η) (η .universal .coinduction (η' .element)) i ∘ᴾ⟨ Q ⟩ f ] ⟩
                 D [ push-elt (_ , C [ η .element ∘ᴾ⟨ P ⟩ η .universal .coinduction (η' .element) ]) .snd ∘ᴾ⟨ Q ⟩ f  ]
                  ≡[ i ]⟨ D [ push-elt (_ , η .universal .commutes (η' .element) i) .snd ∘ᴾ⟨ Q ⟩ f ] ⟩
                 D [ push-elt (elementᴾ _ _ η') .snd ∘ᴾ⟨ Q ⟩ f  ]
                  ≡⟨ f-commutes ⟩
                 ϕ ∎))

{-# OPTIONS --safe #-}
module Cubical.Categories.Presheaf.Representable where

open import Cubical.Data.Sigma
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Yoneda
open import Cubical.Categories.Constructions.Elements
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Limits
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf
open import Cubical.HITs.PropositionalTruncation.Base

private
  variable ℓ ℓ' : Level

open Category
open Contravariant

-- | A representation of a presheaf is an object whose image under the
-- | Yoneda embedding is isomorphic to P
Representation : ∀ {ℓ}{ℓ'} (C : Category ℓ ℓ') (P : Presheaf C ℓ') → Type (ℓ-max ℓ ℓ')
Representation C P = Σ[ A ∈ C .ob ] CatIso (PresheafCategory C _) (C [-, A ]) P

Representable : ∀ {ℓ}{ℓ'} (C : Category ℓ ℓ') (P : Presheaf C ℓ') → Type (ℓ-max ℓ ℓ')
Representable C P = ∥ Representation C P ∥₁

-- | By the Yoneda lemma, the data of a representation is equivalent
-- | to just specifying a universal element of the presheaf
UniversalElement : ∀ {ℓ}{ℓ'} (C : Category ℓ ℓ') (P : Presheaf C ℓ') → Type (ℓ-max ℓ ℓ')
UniversalElement C P = Terminal (∫ᴾ_ {C = C} P)

Representation≅UniversalElement : ∀ {ℓ}{ℓ'} (C : Category ℓ ℓ') (P : Presheaf C ℓ')
                                → Iso (Representation C P) (UniversalElement C P)
Representation≅UniversalElement {ℓ}{ℓ'} C P = iso toUnivElt toRepr η-round-trip repr-round-trip where
  open NatTrans
  toUnivElt : Representation C P → UniversalElement C P
  toUnivElt (A , YoA→P , isiso P→YoA sec ret) = (A , (Iso.fun (yonedaᴾ P A) YoA→P)) , is-universal where
    YoA→P-naturality : ∀ {b c : C .ob} → (f : C [ b , A ]) (g : C [ c , b ])
                     → YoA→P .N-ob c (f ∘⟨ C ⟩ g) ≡ C [ YoA→P .N-ob b f ∘ᴾ⟨ P ⟩ g ]
    YoA→P-naturality f g = λ i → YoA→P .N-hom g i f

    P→YoA-naturality : ∀ {b c : C .ob} → (ϕ : fst (P ⟅ b ⟆)) (g : C [ c , b ])
                     → P→YoA .N-ob c (C [ ϕ ∘ᴾ⟨ P ⟩ g ]) ≡ P→YoA .N-ob b ϕ ∘⟨ C ⟩ g
    P→YoA-naturality ϕ g = λ i → P→YoA .N-hom g i ϕ

    is-universal : isTerminal (∫ᴾ_ {C = C} P) (A , Iso.fun (yonedaᴾ P A) YoA→P )
    is-universal (B , ϕ) = (P→YoA .N-ob B ϕ , commutes) , is-uniq where
      commutes : ϕ ≡ C [ (YoA→P .N-ob A (C .id)) ∘ᴾ⟨ P ⟩ P→YoA .N-ob B ϕ ]
      commutes =
        ϕ                                           ≡⟨ sym (λ i → sec i .N-ob B ϕ) ⟩
        YoA→P .N-ob B (P→YoA .N-ob B ϕ)             ≡⟨ sym (λ i → YoA→P .N-ob B (⋆IdR C (P→YoA .N-ob B ϕ) i)) ⟩
        YoA→P .N-ob B (id C ∘⟨ C ⟩ P→YoA .N-ob B ϕ) ≡⟨ YoA→P-naturality (C .id) (P→YoA .N-ob B ϕ) ⟩
        C [ (YoA→P .N-ob A (C .id)) ∘ᴾ⟨ P ⟩ P→YoA .N-ob B ϕ ] ∎

      is-uniq : (f+ : (∫ᴾ_ {C = C} P) [ (B , ϕ) , (A , Iso.fun (yonedaᴾ P A) YoA→P) ])
              → (P→YoA .N-ob B ϕ , commutes) ≡ f+
      is-uniq f+ @ (f , ϕ=η*f) = ∫ᴾhomEqSimpl {C = C}{F = P} ((P→YoA .N-ob B ϕ , commutes)) f+ reason where
        reason : P→YoA .N-ob B ϕ ≡ f
        reason =
          P→YoA .N-ob B ϕ                                       ≡⟨ (λ i → P→YoA .N-ob B (ϕ=η*f i)) ⟩
          P→YoA .N-ob B (C [ YoA→P .N-ob A (C .id) ∘ᴾ⟨ P ⟩ f ]) ≡⟨ P→YoA-naturality (YoA→P .N-ob A (C .id)) f ⟩
          P→YoA .N-ob A (YoA→P .N-ob A (C .id)) ∘⟨ C ⟩ f        ≡⟨ (λ i → ret i .N-ob A (C .id) ∘⟨ C ⟩ f) ⟩
          C .id ∘⟨ C ⟩ f                                        ≡⟨ ⋆IdR C f ⟩
          f ∎

  toRepr : UniversalElement C P → Representation C P
  toRepr ((A , η) , η-is-universal) =
    A
    , NatIso→FUNCTORIso (C ^op) (SET _)
                        (record { trans = Iso.inv (yonedaᴾ P A) η
                                ; nIso = λ b → isiso (inverses b)
                                                     (funExt (inverses-sec b))
                                                     (funExt (inverses-ret b)) }) where
    inverses : N-ob-Type P (C [-, A ])
    inverses b ϕ = fst (fst (η-is-universal (b , ϕ)))

    inverses-sec : ∀ (b : C .ob) (ϕ : fst (P ⟅ b ⟆))
                 → C [ η ∘ᴾ⟨ P ⟩ (inverses b ϕ) ] ≡ ϕ
    inverses-sec b ϕ with η-is-universal ( b , ϕ)
    ... | (f , ϕ=η*f) , f-uniq = sym ϕ=η*f

    inverses-ret : ∀ (b : C .ob) (f : C [ b , A ])
                 → inverses b (C [ η ∘ᴾ⟨ P ⟩ f ]) ≡ f
    inverses-ret b f with η-is-universal (b , (C [ η ∘ᴾ⟨ P ⟩ f ]))
    ... | (g , η⋆f=η⋆g) , g-uniq = λ i → fst (g-uniq (f , refl) i)

  η-round-trip : section toUnivElt toRepr
  η-round-trip ((A , η) , η-is-universal) =
    Σ≡Prop (isPropIsTerminal (∫ᴾ_ {C = C} P))
           (ΣPathP (refl , Iso.rightInv (yonedaᴾ {C = C} P A) η))

  repr-round-trip : retract toUnivElt toRepr
  repr-round-trip (A , YoA→P , isiso P→YoA sec ret) =
    ΣPathP (refl , Σ≡Prop isPropIsIso (Iso.leftInv (yonedaᴾ {C = C} P A) YoA→P))

RepresentationToUniversalElement : ∀ {ℓ}{ℓ'} (C : Category ℓ ℓ') (P : Presheaf C ℓ')
                                → (Representation C P) → (UniversalElement C P)
RepresentationToUniversalElement C P = Iso.fun (Representation≅UniversalElement C P)

UniversalElementToRepresentation : ∀ {ℓ}{ℓ'} (C : Category ℓ ℓ') (P : Presheaf C ℓ')
                                 → (UniversalElement C P) → (Representation C P)
UniversalElementToRepresentation C P = Iso.inv (Representation≅UniversalElement C P)

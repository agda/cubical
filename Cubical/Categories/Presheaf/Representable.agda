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
open import Cubical.Categories.Presheaf.Base
open import Cubical.HITs.PropositionalTruncation.Base

private
  variable ℓ ℓ' : Level

open Category
open Contravariant

-- | A representation of a presheaf is an object whose image under the
-- | Yoneda embedding is isomorphic to P
-- | We define only the maximally universe polymorphic version, the
-- | Lifts don't appear in practice because we usually use universal
-- | elements instead

module _ {ℓo}{ℓh}{ℓp} (C : Category ℓo ℓh) (P : Presheaf C ℓp) where

  Representation : Type (ℓ-max (ℓ-max ℓo ℓh) ℓp)
  Representation =
    Σ[ A ∈ C .ob ]
    CatIso (PresheafCategory C (ℓ-max ℓh ℓp))
         (LiftF {ℓ = ℓh}{ℓ' = ℓp} ∘F (C [-, A ]))
         (LiftF {ℓ = ℓp}{ℓ' = ℓh} ∘F P)

  Representable : Type (ℓ-max (ℓ-max ℓo ℓh) ℓp)
  Representable = ∥ Representation ∥₁

  -- | By the Yoneda lemma, the data of a representation is equivalent
  -- | to just specifying a universal element of the presheaf
  UniversalElement : Type (ℓ-max (ℓ-max ℓo ℓh) ℓp)
  UniversalElement = Terminal (∫ᴾ_ {C = C} P)

  hasUniversalElement : Type (ℓ-max (ℓ-max ℓo ℓh) ℓp)
  hasUniversalElement = ∥ UniversalElement ∥₁

  module _ (η : UniversalElement) where
    vertex : C .ob
    vertex = η .fst .fst

    element : (P ⟅ vertex ⟆) .fst
    element = η .fst .snd

  open NatTrans
  Representation≅UniversalElement : Iso Representation UniversalElement
  Representation≅UniversalElement .Iso.fun (A , YoA→P , YoA→P-isIso) .fst .fst = A
  Representation≅UniversalElement .Iso.fun (A , YoA→P , YoA→P-isIso) .fst .snd = Iso.fun (yonedaᴾPoly P A) YoA→P
  Representation≅UniversalElement .Iso.fun (A , YoA→P , isiso P→YoA sec ret) .snd (B , ϕ) .fst .fst = P→YoA .N-ob B (lift ϕ) .lower
  Representation≅UniversalElement .Iso.fun (A , YoA→P , isiso P→YoA sec ret) .snd (B , ϕ) .fst .snd =
    ϕ                                             ≡[ i ]⟨ (sec (~ i) .N-ob B (lift ϕ)) .lower ⟩
    YoA→P .N-ob B (P→YoA .N-ob B (lift ϕ)) .lower ≡[ i ]⟨ YoA→P .N-ob B (lift (C .⋆IdR (P→YoA .N-ob B (lift ϕ) .lower) (~ i))) .lower ⟩
    (YoA→P .N-ob B (lift (C .id ∘⟨ C ⟩ P→YoA .N-ob B (lift ϕ) .lower))) .lower ≡[ i ]⟨ YoA→P .N-hom (P→YoA .N-ob B (lift ϕ) .lower) i (lift (C .id)) .lower ⟩
    C [ YoA→P .N-ob A (lift (C .id)) .lower ∘ᴾ⟨ P ⟩ P→YoA .N-ob B (lift ϕ) .lower ] ∎
  Representation≅UniversalElement .Iso.fun (A , YoA→P , isiso P→YoA sec ret) .snd (B , ϕ) .snd f+ @ (f , ϕ=η∘f) = ∫ᴾhomEqSimpl {C = C}{F = P} ((P→YoA .N-ob B (lift ϕ) .lower) , _) f+
    (P→YoA .N-ob B (lift ϕ) .lower
      ≡[ i ]⟨ P→YoA .N-ob B (lift (ϕ=η∘f i)) .lower ⟩
    P→YoA .N-ob B (lift (C [ YoA→P .N-ob A (lift (C .id)) .lower ∘ᴾ⟨ P ⟩ f ])) .lower
      ≡[ i ]⟨ P→YoA .N-hom f i (YoA→P .N-ob A (lift (C .id))) .lower ⟩
    P→YoA .N-ob A (YoA→P .N-ob A (lift (C .id))) .lower ∘⟨ C ⟩ f
      ≡[ i ]⟨ ret i .N-ob A (lift (C .id)) .lower ∘⟨ C ⟩ f ⟩
    C .id ∘⟨ C ⟩ f
      ≡⟨ C .⋆IdR f ⟩
    f ∎)
  Representation≅UniversalElement .Iso.inv ((A , η) , η-is-universal) .fst = A
  Representation≅UniversalElement .Iso.inv ((A , η) , η-is-universal) .snd = NatIso→FUNCTORIso (C ^op) (SET _) the-niso where
    the-niso : NatIso (LiftF ∘F (C [-, A ])) (LiftF ∘F P)
    the-niso .NatIso.trans = Iso.inv (yonedaᴾPoly P A) η
    the-niso .NatIso.nIso b = isiso (inverses b) (funExt inverses-sec) (funExt inverses-ret) where
      inverses : N-ob-Type (LiftF ∘F P) (LiftF ∘F (C [-, A ]))
      inverses b ϕ = lift (η-is-universal (b , ϕ .lower) .fst .fst)
  
      inverses-sec : ∀ (ϕ : Lift (fst (P ⟅ b ⟆)))
                   → C [ lift η ∘ᴾ⟨ LiftF ∘F P ⟩ ((inverses b ϕ) .lower) ] ≡ ϕ
      inverses-sec ϕ with η-is-universal (b , ϕ .lower)
      ... | (f , ϕ=η∘f) , _ = λ i → lift (ϕ=η∘f (~ i))
  
      inverses-ret : ∀ (f : Lift (C [ b , A ]))
                   → inverses b (C [ lift η ∘ᴾ⟨ LiftF ∘F P ⟩ f .lower ]) ≡ f
      inverses-ret f i = lift (η-is-universal (b , C [ η ∘ᴾ⟨ P ⟩ f .lower ]) .snd (f .lower , refl) i .fst)
  Representation≅UniversalElement .Iso.rightInv ((A , η) , _) = Σ≡Prop (isPropIsTerminal (∫ᴾ_ {C = C} P)) (ΣPathP (refl , yonedaᴾPoly {C = C} P A .rightInv η))
    where open Iso
  Representation≅UniversalElement .Iso.leftInv (A , YoA→P , _)= ΣPathP (refl , (Σ≡Prop isPropIsIso (yonedaᴾPoly {C = C} P A .leftInv YoA→P)))
    where open Iso

  RepresentationToUniversalElement : Representation → UniversalElement
  RepresentationToUniversalElement = Iso.fun Representation≅UniversalElement

  UniversalElementToRepresentation : UniversalElement → Representation
  UniversalElementToRepresentation = Iso.inv Representation≅UniversalElement

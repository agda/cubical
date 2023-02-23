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

  record isUniversal (η : Elementᴾ {C = C} P) : Type (ℓ-max (ℓ-max ℓo ℓh) ℓp) where
    private
      vertex = η .fst
      element = η .snd
    field
      coinduction : ∀ {b} → (P ⟅ b ⟆) .fst → C [ b , vertex ]
      commutes : ∀ {b} (ϕ : (P ⟅ b ⟆) .fst) → C [ element ∘ᴾ⟨ P ⟩ coinduction ϕ ] ≡ ϕ
      is-uniq : ∀ {b} (ϕ : (P ⟅ b ⟆) .fst) f → (C [ element ∘ᴾ⟨ P ⟩ f ] ≡ ϕ) → f ≡ coinduction ϕ

  record UnivElt : Type (ℓ-max (ℓ-max ℓo ℓh) ℓp) where
    field
      vertex : C .ob
      element : (P ⟅ vertex ⟆) .fst
      universal : isUniversal (vertex , element)

  open UnivElt
  open isUniversal

  elementᴾ : UnivElt → Elementᴾ {C = C} P
  elementᴾ η = (η .vertex , η .element)

  private
    univEltMor : ∀ η {η' : Elementᴾ {C = C} P} → (η'-univ : isUniversal η') → C [ η .fst , η' .fst ]
    univEltMor η η'-univ = η'-univ .coinduction (η .snd)

    univEltLemma : ∀ {η η' : Elementᴾ {C = C} P} → (η-univ : isUniversal η) → (η'-univ : isUniversal η') →
                 univEltMor η η'-univ ∘⟨ C ⟩ univEltMor η' η-univ ≡ C .id
    univEltLemma {η}{η'} η-univ η'-univ =
      η'-univ .coinduction (η .snd) ∘⟨ C ⟩ η-univ .coinduction (η' .snd)
        ≡⟨ η'-univ .is-uniq (η' .snd) _ lem ⟩
      η'-univ .coinduction (η' .snd)
        ≡⟨ sym (η'-univ .is-uniq _ (C .id) (∘ᴾId C P (η' .snd))) ⟩
      C .id ∎ where

      lem : (C [ η' .snd ∘ᴾ⟨ P ⟩ η'-univ .coinduction (η .snd) ∘⟨ C ⟩ η-univ .coinduction (η' .snd) ]) ≡ η' .snd
      lem =
        (C [ η' .snd ∘ᴾ⟨ P ⟩ η'-univ .coinduction (η .snd) ∘⟨ C ⟩ η-univ .coinduction (η' .snd) ])
          ≡⟨ ∘ᴾAssoc C P _ _ _ ⟩
        (C [ C [ η' .snd ∘ᴾ⟨ P ⟩ η'-univ .coinduction (η .snd) ] ∘ᴾ⟨ P ⟩ η-univ .coinduction (η' .snd) ])
          ≡[ i ]⟨ C [ η'-univ .commutes (η .snd) i ∘ᴾ⟨ P ⟩ η-univ .coinduction (η' .snd) ] ⟩
        (C [ η .snd ∘ᴾ⟨ P ⟩ η-univ .coinduction (η' .snd) ])
          ≡⟨ η-univ .commutes _ ⟩
        η' .snd ∎

  univEltIso : ∀ {η η' : Elementᴾ {C = C} P} → isUniversal η → isUniversal η'
             → CatIso C (η .fst) (η' .fst)
  univEltIso {η}{η'} η-univ η'-univ .fst = univEltMor η η'-univ
  univEltIso {η}{η'} η-univ η'-univ .snd .isIso.inv = univEltMor η' η-univ
  univEltIso {η}{η'} η-univ η'-univ .snd .isIso.sec = univEltLemma η-univ η'-univ

  univEltIso {η}{η'} η-univ η'-univ .snd .isIso.ret = univEltLemma η'-univ η-univ

  UniversalElement→UnivElt : UniversalElement → UnivElt
  UniversalElement→UnivElt η .vertex = η .fst .fst
  UniversalElement→UnivElt η .element = η .fst .snd
  UniversalElement→UnivElt η .universal .coinduction ϕ = η .snd (_ , ϕ) .fst .fst
  UniversalElement→UnivElt η .universal .commutes ϕ = sym (η .snd (_ , ϕ) .fst .snd)
  UniversalElement→UnivElt η .universal .is-uniq ϕ f f-commutes i = η .snd (_ , ϕ) .snd (f , sym f-commutes) (~ i) .fst

  UnivElt→UniversalElement : UnivElt → UniversalElement
  UnivElt→UniversalElement η .fst .fst = η .vertex
  UnivElt→UniversalElement η .fst .snd = η .element
  UnivElt→UniversalElement η .snd (b , ϕ) .fst .fst = η .universal .coinduction ϕ
  UnivElt→UniversalElement η .snd (b , ϕ) .fst .snd = sym (η .universal .commutes ϕ)
  UnivElt→UniversalElement η .snd (b , ϕ) .snd (f , f-commutes) = Σ≡Prop (λ x → (P ⟅ b ⟆) .snd _ _) (sym (η .universal .is-uniq ϕ f (sym f-commutes)))

  UniversalElement≅UnivElt : Iso UniversalElement UnivElt
  UniversalElement≅UnivElt .Iso.fun = UniversalElement→UnivElt
  UniversalElement≅UnivElt .Iso.inv = UnivElt→UniversalElement
  UniversalElement≅UnivElt .Iso.rightInv η = refl
  UniversalElement≅UnivElt .Iso.leftInv η = ΣPathP (refl , (funExt (λ (b , ϕ) → ΣPathP (refl , (funExt (λ (f , f-commutes) → ∫ᴾ_ {C = C} P .isSetHom _ _ _ _))))))

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
  Representation≅UniversalElement .Iso.inv ((A , η) , η-univ) .fst = A
  Representation≅UniversalElement .Iso.inv ((A , η) , η-univ) .snd = NatIso→FUNCTORIso (C ^op) (SET _) the-niso where
    the-niso : NatIso (LiftF ∘F (C [-, A ])) (LiftF ∘F P)
    the-niso .NatIso.trans = Iso.inv (yonedaᴾPoly P A) η
    the-niso .NatIso.nIso b = isiso (inverses b) (funExt inverses-sec) (funExt inverses-ret) where
      inverses : N-ob-Type (LiftF ∘F P) (LiftF ∘F (C [-, A ]))
      inverses b ϕ = lift (η-univ (b , ϕ .lower) .fst .fst)

      inverses-sec : ∀ (ϕ : Lift (fst (P ⟅ b ⟆)))
                   → C [ lift η ∘ᴾ⟨ LiftF ∘F P ⟩ ((inverses b ϕ) .lower) ] ≡ ϕ
      inverses-sec ϕ with η-univ (b , ϕ .lower)
      ... | (f , ϕ=η∘f) , _ = λ i → lift (ϕ=η∘f (~ i))

      inverses-ret : ∀ (f : Lift (C [ b , A ]))
                   → inverses b (C [ lift η ∘ᴾ⟨ LiftF ∘F P ⟩ f .lower ]) ≡ f
      inverses-ret f i = lift (η-univ (b , C [ η ∘ᴾ⟨ P ⟩ f .lower ]) .snd (f .lower , refl) i .fst)
  Representation≅UniversalElement .Iso.rightInv ((A , η) , _) = Σ≡Prop (isPropIsTerminal (∫ᴾ_ {C = C} P)) (ΣPathP (refl , yonedaᴾPoly {C = C} P A .rightInv η))
    where open Iso
  Representation≅UniversalElement .Iso.leftInv (A , YoA→P , _)= ΣPathP (refl , (Σ≡Prop isPropIsIso (yonedaᴾPoly {C = C} P A .leftInv YoA→P)))
    where open Iso

  RepresentationToUniversalElement : Representation → UniversalElement
  RepresentationToUniversalElement = Iso.fun Representation≅UniversalElement

  UniversalElementToRepresentation : UniversalElement → Representation
  UniversalElementToRepresentation = Iso.inv Representation≅UniversalElement

  Representation≅UnivElt : Iso Representation UnivElt
  Representation≅UnivElt = compIso Representation≅UniversalElement UniversalElement≅UnivElt

  RepresentationToUnivElt : Representation → UnivElt
  RepresentationToUnivElt = Iso.fun Representation≅UnivElt

  UnivEltToRepresentation : UnivElt → Representation
  UnivEltToRepresentation = Iso.inv Representation≅UnivElt

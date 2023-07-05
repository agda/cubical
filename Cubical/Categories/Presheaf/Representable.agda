{-# OPTIONS --safe #-}
module Cubical.Categories.Presheaf.Representable where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation.Base

open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.Elements
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Limits
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Properties
open import Cubical.Categories.Yoneda

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
    Σ[ A ∈ C .ob ] PshIso C (C [-, A ]) P

  Representable : Type (ℓ-max (ℓ-max ℓo ℓh) ℓp)
  Representable = ∥ Representation ∥₁

  Elements = ∫ᴾ_ {C = C} P
  -- | By the Yoneda lemma, the data of a representation is equivalent
  -- | to just specifying a universal element of the presheaf
  UniversalElement : Type (ℓ-max (ℓ-max ℓo ℓh) ℓp)
  UniversalElement = Terminal Elements

  hasUniversalElement : Type (ℓ-max (ℓ-max ℓo ℓh) ℓp)
  hasUniversalElement = ∥ UniversalElement ∥₁

  -- A packaged record version that is easier to use
  record isUniversal (η : Elementᴾ {C = C} P) : Type (ℓ-max (ℓ-max ℓo ℓh) ℓp)
         where
    private
      vertex = η .fst
      element = η .snd
    field
      coinduction : ∀ {b} → (P ⟅ b ⟆) .fst → C [ b , vertex ]
      commutes : ∀ {b} (ϕ : (P ⟅ b ⟆) .fst)
               → element ∘ᴾ⟨ C , P ⟩ coinduction ϕ ≡ ϕ
      is-uniq : ∀ {b} (ϕ : (P ⟅ b ⟆) .fst) f
              → (element ∘ᴾ⟨ C , P ⟩ f ≡ ϕ)
              → f ≡ coinduction ϕ

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
    univEltMor : ∀ η {η' : Elementᴾ {C = C} P}
               → (η'-univ : isUniversal η')
               → C [ η .fst , η' .fst ]
    univEltMor η η'-univ = η'-univ .coinduction (η .snd)

    univEltLemma : ∀ {η η' : Elementᴾ {C = C} P}
                 → (η-univ : isUniversal η)
                 → (η'-univ : isUniversal η')
                 → univEltMor η η'-univ ∘⟨ C ⟩ univEltMor η' η-univ ≡ C .id
    univEltLemma {η}{η'} η-univ η'-univ =
      η'-univ .coinduction (η .snd) ∘⟨ C ⟩ η-univ .coinduction (η' .snd)
        ≡⟨ η'-univ .is-uniq (η' .snd) _ lem ⟩
      η'-univ .coinduction (η' .snd)
        ≡⟨ sym (η'-univ .is-uniq _ (C .id) (∘ᴾId C P (η' .snd))) ⟩
      C .id ∎ where

      lem : (η' .snd
               ∘ᴾ⟨ C , P ⟩ (η'-univ .coinduction (η .snd)
               ∘⟨ C ⟩ η-univ .coinduction (η' .snd)))
            ≡ η' .snd
      lem =
        ∘ᴾAssoc C P _ _ _
        ∙ (λ i → η'-univ .commutes (η .snd) i ∘ᴾ⟨ C , P ⟩ η-univ .coinduction (η' .snd))
        ∙ η-univ .commutes _

  univEltIso : ∀ {η η' : Elementᴾ {C = C} P} → isUniversal η → isUniversal η'
             → CatIso C (η .fst) (η' .fst)
  univEltIso {η}{η'} η-univ η'-univ .fst = univEltMor η η'-univ
  univEltIso {η}{η'} η-univ η'-univ .snd .isIso.inv = univEltMor η' η-univ
  univEltIso {η}{η'} η-univ η'-univ .snd .isIso.sec = univEltLemma η-univ η'-univ
  univEltIso {η}{η'} η-univ η'-univ .snd .isIso.ret = univEltLemma η'-univ η-univ

  -- First the logical equivalence
  isTerminalElement→isUniversal : ∀ {η : Elementᴾ {C = C} P}
                                → isTerminal Elements η → isUniversal η
  isTerminalElement→isUniversal {η} term .coinduction ϕ = term (_ , ϕ) .fst .fst
  isTerminalElement→isUniversal term .commutes ϕ = sym (term (_ , ϕ) .fst .snd)
  isTerminalElement→isUniversal term .is-uniq ϕ f commutes i =
    term (_ , ϕ) .snd (f , sym commutes) (~ i) .fst

  isUniversal→isTerminalElement : ∀ {η : Elementᴾ {C = C} P} → isUniversal η
                                → isTerminal Elements η
  isUniversal→isTerminalElement η-univ ϕ .fst .fst =
    η-univ .coinduction (ϕ .snd)
  isUniversal→isTerminalElement η-univ ϕ .fst .snd =
    sym (η-univ .commutes (ϕ .snd))
  isUniversal→isTerminalElement η-univ ϕ .snd f =
    Σ≡Prop (λ x → (P ⟅ _ ⟆) .snd _ _)
           (sym (η-univ .is-uniq (ϕ .snd) (f .fst) (sym (f .snd))))

  isPropIsUniversal : ∀ η → isProp (isUniversal η)
  isPropIsUniversal η =
    isPropRetract isUniversal→isTerminalElement
                  isTerminalElement→isUniversal
                  reason
                  (isPropIsTerminal Elements η) where
    reason : (x : isUniversal (η .fst , η .snd))
           → isTerminalElement→isUniversal (isUniversal→isTerminalElement x) ≡ x
    reason η-univ i .coinduction ϕ = η-univ .coinduction ϕ
    reason η-univ i .commutes ϕ = η-univ .commutes ϕ
    reason η-univ i .is-uniq ϕ f commutes = η-univ .is-uniq ϕ f commutes

  UniversalElement→UnivElt : UniversalElement → UnivElt
  UniversalElement→UnivElt η .vertex = η .fst .fst
  UniversalElement→UnivElt η .element = η .fst .snd
  UniversalElement→UnivElt η .universal = isTerminalElement→isUniversal (η .snd)

  UnivElt→UniversalElement : UnivElt → UniversalElement
  UnivElt→UniversalElement η .fst .fst = η .vertex
  UnivElt→UniversalElement η .fst .snd = η .element
  UnivElt→UniversalElement η .snd = isUniversal→isTerminalElement (η .universal)

  UniversalElement≅UnivElt : Iso UniversalElement UnivElt
  UniversalElement≅UnivElt .Iso.fun = UniversalElement→UnivElt
  UniversalElement≅UnivElt .Iso.inv = UnivElt→UniversalElement
  UniversalElement≅UnivElt .Iso.rightInv η = refl
  UniversalElement≅UnivElt .Iso.leftInv η =
    Σ≡Prop (isPropIsTerminal Elements) refl

  open NatTrans
  isTerminalElement→YoIso : (η : Terminal Elements)
    → Cubical.Categories.Category.isIso
       (PresheafCategory C (ℓ-max ℓh ℓp))
       (Iso.inv (yonedaᴾ* {C = C} P (η .fst .fst)) (η .fst .snd))
  isTerminalElement→YoIso ((A , η) , η-univ) =
    FUNCTORIso (C ^op) (SET (ℓ-max ℓh ℓp)) _ pointwise where
    pointwise : ∀ c →
      Cubical.Categories.Category.isIso (SET (ℓ-max ℓh ℓp))
        (Iso.inv (yonedaᴾ* {C = C} P A) η ⟦ c ⟧)
    pointwise c .isIso.inv ϕ = lift (η-univ (_ , ϕ .lower) .fst .fst)
    pointwise c .isIso.sec =
      funExt (λ ϕ i → lift (η-univ (_ , ϕ .lower) .fst .snd (~ i)))
    pointwise c .isIso.ret =
      funExt (λ f i →
        lift (η-univ (_ , η ∘ᴾ⟨ C , P ⟩ f .lower)
              .snd (f .lower , refl) i .fst))

  YoIso→isTerminalElement :
    ∀ A
    → (i : PshIso C (C [-, A ]) P)
    → isTerminal Elements (A , (i .fst .N-ob A (lift (C .id)) .lower))
  YoIso→isTerminalElement A (YoA→P , isiso P→YoA sec ret) (B , ϕ) .fst .fst =
    P→YoA .N-ob B (lift ϕ) .lower
  YoIso→isTerminalElement A (YoA→P , isiso P→YoA sec ret) (B , ϕ) .fst .snd =
    (λ i → (sec (~ i) .N-ob B (lift ϕ)) .lower)
    ∙ (λ i → YoA→P .N-ob B (lift (C .⋆IdR (P→YoA .N-ob B (lift ϕ) .lower) (~ i))) .lower)
    ∙ λ i → YoA→P .N-hom (P→YoA .N-ob B (lift ϕ) .lower) i (lift (C .id)) .lower
  YoIso→isTerminalElement A (YoA→P , isiso P→YoA sec ret)
                            (B , ϕ) .snd
                            f+ @ (f , ϕ=η∘f)
    = ∫ᴾhomEqSimpl {C = C}{F = P} ((P→YoA .N-ob B (lift ϕ) .lower) , _) f+
    (P→YoA .N-ob B (lift ϕ) .lower
      ≡[ i ]⟨ P→YoA .N-ob B (lift (ϕ=η∘f i)) .lower ⟩
    P→YoA .N-ob B (lift (YoA→P .N-ob A (lift (C .id)) .lower ∘ᴾ⟨ C , P ⟩ f ))
      .lower
      ≡[ i ]⟨ P→YoA .N-hom f i (YoA→P .N-ob A (lift (C .id))) .lower ⟩
    P→YoA .N-ob A (YoA→P .N-ob A (lift (C .id))) .lower ∘⟨ C ⟩ f
      ≡[ i ]⟨ ret i .N-ob A (lift (C .id)) .lower ∘⟨ C ⟩ f ⟩
    C .id ∘⟨ C ⟩ f
      ≡⟨ C .⋆IdR f ⟩
    f ∎)

  RepresentationToUniversalElement : Representation → UniversalElement
  RepresentationToUniversalElement (A , YoA→P , YoA→P-isIso) .fst .fst = A
  RepresentationToUniversalElement (A , YoA→P , YoA→P-isIso) .fst .snd =
    Iso.fun (yonedaᴾ* P A) YoA→P
  RepresentationToUniversalElement (A , YoA→P , YoA→P-isIso) .snd =
    YoIso→isTerminalElement A (YoA→P , YoA→P-isIso)

  UniversalElementToRepresentation : UniversalElement → Representation
  UniversalElementToRepresentation ((A , η) , η-univ) .fst = A
  UniversalElementToRepresentation η-terminal @ ((A , η) , η-univ) .snd =
    (Iso.inv (yonedaᴾ* P A) η) , isTerminalElement→YoIso η-terminal

  Representation≅UniversalElement : Iso Representation UniversalElement
  Representation≅UniversalElement .Iso.fun = RepresentationToUniversalElement
  Representation≅UniversalElement .Iso.inv = UniversalElementToRepresentation
  Representation≅UniversalElement .Iso.rightInv ((A , η) , _) =
    Σ≡Prop (isPropIsTerminal Elements)
           (ΣPathP (refl , yonedaᴾ* {C = C} P A .rightInv η))
    where open Iso
  Representation≅UniversalElement .Iso.leftInv (A , YoA→P , _) =
    ΣPathP (refl , (Σ≡Prop isPropIsIso (yonedaᴾ* {C = C} P A .leftInv YoA→P)))
    where open Iso

  Representation≅UnivElt : Iso Representation UnivElt
  Representation≅UnivElt =
    compIso Representation≅UniversalElement UniversalElement≅UnivElt

  RepresentationToUnivElt : Representation → UnivElt
  RepresentationToUnivElt = Iso.fun Representation≅UnivElt

  UnivEltToRepresentation : UnivElt → Representation
  UnivEltToRepresentation = Iso.inv Representation≅UnivElt

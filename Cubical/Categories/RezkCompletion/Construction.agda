{-

The Construction of Rezk Completion

-}
{-# OPTIONS --safe --lossy-unification #-}

module Cubical.Categories.RezkCompletion.Construction where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport hiding (pathToIso)
open import Cubical.Foundations.Isomorphism using (isoToPath; Iso; isoToIsEquiv; iso)
open import Cubical.Foundations.Univalence using (uaβ)
open import Cubical.Foundations.Equiv.Base
open import Cubical.Functions.FunExtEquiv
open import Cubical.Functions.Surjection
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁; ∣_∣₁; isPropPropTrunc)
open import Cubical.HITs.GroupoidQuotients as GQ using (_//_; [_]; eq//; comp//; squash//)

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Equivalence.WeakEquivalence
open import Cubical.Categories.Constructions.EssentialImage
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Yoneda
open import Cubical.Categories.Isomorphism

open import Cubical.Categories.RezkCompletion.Base

private variable
  ℓ ℓ' ℓ'' ℓ''' : Level

open isWeakEquivalence


-- There are two different ways to construct the Rezk completion,
-- one is using the essential image of the Yoneda embbeding,
-- another one is using a higher inductive type
-- (c.f. HoTT Book Chaper 9.9).

-- Yoneda embbeding can give a very simple and quick construction.
-- Unfortunately, this construction increases the universe level.

-- The HIT construction, on the other hand, keeps the universe level,
-- but its proof is a bit long and tedious, still easy though.


{- The Construction by Yoneda Embedding -}

module RezkByYoneda (C : Category ℓ ℓ) where

  YonedaImage : Category (ℓ-suc ℓ) ℓ
  YonedaImage = EssentialImage (YO {C = C})

  isUnivalentYonedaImage : isUnivalent YonedaImage
  isUnivalentYonedaImage = isUnivalentEssentialImage _ isUnivalentPresheafCategory

  ToYonedaImage : Functor C YonedaImage
  ToYonedaImage = ToEssentialImage _

  isWeakEquivalenceToYonedaImage : isWeakEquivalence ToYonedaImage
  isWeakEquivalenceToYonedaImage .fullfaith = isFullyFaithfulToEssentialImage YO isFullyFaithfulYO
  isWeakEquivalenceToYonedaImage .esssurj   = isEssentiallySurjToEssentialImage YO

  isRezkCompletionToYonedaImage : isRezkCompletion ToYonedaImage
  isRezkCompletionToYonedaImage = makeIsRezkCompletion isUnivalentYonedaImage isWeakEquivalenceToYonedaImage


{- The Construction by Higher Inductive Type -}

module RezkByHIT (C : Category ℓ ℓ') where
  module C = Category C
  open Category hiding (_∘_)
  open isUnivalent
  open Functor
  open isIso

  private
    variable
      x y z w : ob C

    IsoC : ob C → ob C → Type ℓ'
    IsoC = CatIso C

    ⋆IsoC : ∀ x y z → IsoC x y → IsoC y z → IsoC x z
    ⋆IsoC x y z = ⋆Iso

  RezkOb : Type (ℓ-max ℓ ℓ')
  RezkOb = ob C // ⋆IsoC

  inc : ob C → RezkOb
  inc = [_]

  inc-ua : IsoC x y → inc x ≡ inc y
  inc-ua = eq//

  inc-sq : (f : IsoC x y) (g : IsoC y z) → Square (inc-ua f) (inc-ua (⋆Iso f g)) refl (inc-ua g)
  inc-sq = comp//

  squash : isGroupoid RezkOb
  squash = squash//

  elim : {P : RezkOb → Type ℓ''} → _ → (f : _) → (feq : _) → _ → ∀ x → P x
  elim = GQ.elim {A = ob C} ⋆IsoC

  elimSet : {P : RezkOb → Type ℓ''} → _ → (f : _) → _ → ∀ x → P x
  elimSet = GQ.elimSet {A = ob C} ⋆IsoC

  elimProp : {P : RezkOb → Type ℓ''} → _ → _ → ∀ x → P x
  elimProp = GQ.elimProp {A = ob C} ⋆IsoC

  rec : {P : Type ℓ''} → _ → (f : _) → (feq : _) → _ → RezkOb → P
  rec = GQ.rec {A = ob C} ⋆IsoC

  module _ {P : RezkOb → RezkOb → Type ℓ''}
    (P-Set : ∀ x y → isSet (P x y))
    (P-inc : ∀ x y → P (inc x) (inc y))
    (P-inc-ua : ∀ {x y z} f
              → PathP (λ i → P (inc x) (inc-ua f i)) (P-inc x y) (P-inc x z))
    (P-ua-inc : ∀ {x y z} f
              → PathP (λ i → P (inc-ua f i) (inc z)) (P-inc x z) (P-inc y z))
    where

    elimSet₂ : ∀ x y → P x y
    elimSet₂ = elimSet (λ x → isSetΠ (P-Set x)) (λ x → elimSet (P-Set (inc x)) (P-inc x) P-inc-ua) λ f →
      funExt (elimProp (λ x → isOfHLevelPathP' 1 (P-Set _ _) _ _) λ x → P-ua-inc f)

  module _ {P : RezkOb → RezkOb → Type ℓ''}
    (P-Prop : ∀ x y → isProp (P x y))
    (P-inc : ∀ x y → P (inc x) (inc y))
    where

    elimProp₂ : ∀ x y → P x y
    elimProp₂ = elimProp (λ x → isPropΠ (P-Prop x)) λ x → elimProp (P-Prop (inc x)) (P-inc x)

  module _ {P : RezkOb → RezkOb → RezkOb → Type ℓ''}
    (P-Set : ∀ x y z → isSet (P x y z))
    (P-inc : ∀ x y z → P (inc x) (inc y) (inc z))
    (P-ua₁ : ∀ {x y z w} f
           → PathP (λ i → P (inc x) (inc y) (inc-ua f i)) (P-inc x y z) (P-inc x y w))
    (P-ua₂ : ∀ {x y z w} f
           → PathP (λ i → P (inc x) (inc-ua f i) (inc w)) (P-inc x y w) (P-inc x z w))
    (P-ua₃ : ∀ {x y z w} f
           → PathP (λ i → P (inc-ua f i) (inc z) (inc w)) (P-inc x z w) (P-inc y z w))
    where

    elimSet₃ : ∀ x y z → P x y z
    elimSet₃ = elimSet (λ x → isSetΠ2 (P-Set x)) (λ x → elimSet₂ (P-Set (inc x)) (P-inc x) P-ua₁ P-ua₂) λ f → funExt₂ $
      elimProp₂ (λ x y → isOfHLevelPathP' 1 (P-Set _ _ _) _ _) λ x y → P-ua₃ f

  module _ {P : Type ℓ''}
    (P-Grpd : isGroupoid P)
    (P-inc : ob C → ob C → P)
    (P-inc-ua : ∀ {x y z} → IsoC y z → P-inc x y ≡ P-inc x z)
    (P-ua-inc : ∀ {x y z} → IsoC x y → P-inc x z ≡ P-inc y z)
    (P-ua-inc-ua : ∀ {x y z w} (g : IsoC z w) (f : IsoC x y)
      → Square (P-ua-inc g) (P-ua-inc g) (P-inc-ua f) (P-inc-ua f))
    (P-inc-sq : ∀ {x y z w} (f : IsoC y z) (g : IsoC z w)
      → Square (P-inc-ua {x = x} f) (P-inc-ua (⋆Iso f g)) refl (P-inc-ua g))
    (P-sq-inc : ∀ {x y z w} (f : IsoC x y) (g : IsoC y z)
      → Square (P-ua-inc {z = w} f) (P-ua-inc (⋆Iso f g)) refl (P-ua-inc g))
    where

    rec₂ : RezkOb → RezkOb → P
    rec₂ = rec (isGroupoidΠ λ _ → P-Grpd)
      (λ x → rec P-Grpd (P-inc x) P-inc-ua P-inc-sq)
      (λ f → funExt (elimSet (λ _ → P-Grpd _ _) (λ _ → P-ua-inc f) (P-ua-inc-ua f)))
      (λ f g → congP (λ _ → funExt) (funExt (elimProp (λ x → isOfHLevelPathP' 1 (P-Grpd _ _) _ _) λ x → P-sq-inc f g)))

  module _ (P : Category ℓ'' ℓ''') (P-univ : isUnivalent P) (P-inc : Functor C P)
    where

    recCat : RezkOb → ob P
    recCat = rec (isGroupoid-ob P-univ) (P-inc .F-ob)
                 (CatIsoToPath P-univ ∘ F-Iso {F = P-inc}) λ f g →
      congP (λ _ → CatIsoToPath P-univ) $
        subst⁻ (PathP _ (F-Iso {F = P-inc} f)) (F-Iso-Pres⋆ f g) $
          transportIsoToPathIso P-univ _ _

  inc-⋆ : (f : IsoC x y) (g : IsoC y z) → inc-ua (⋆Iso f g) ≡ inc-ua f ∙ inc-ua g
  inc-⋆ = GQ.comp'// _ ⋆IsoC

  inc-id : inc-ua (idCatIso {x = x}) ≡ refl
  inc-id =
    incId ≡⟨ sym (compPathr-cancel (sym incId) incId) ⟩
    (incId ∙ incId) ∙ sym incId ≡⟨ congL _∙_ (sym (inc-⋆ idCatIso idCatIso)) ⟩
    inc-ua (⋆Iso idCatIso idCatIso) ∙ sym incId ≡⟨ congL _∙_ (cong inc-ua (⋆IsoIdL _)) ⟩
    incId ∙ sym incId ≡⟨ rCancel incId ⟩
    refl ∎
    where incId = inc-ua idCatIso

  inc-inv : (f : IsoC x y) → inc-ua (invIso f) ≡ sym (inc-ua f)
  inc-inv f =
    inc-ua (invIso f) ≡⟨ sym (compPathr-cancel (sym (inc-ua f)) (inc-ua (invIso f))) ⟩
    (inc-ua (invIso f) ∙ inc-ua f) ∙ sym (inc-ua f) ≡⟨ congL _∙_ (sym (inc-⋆ (invIso f) f)) ⟩
    inc-ua (⋆Iso (invIso f) f) ∙ sym (inc-ua f) ≡⟨ congL _∙_ (cong inc-ua (CatIso≡ _ _ (f .snd .sec))) ⟩
    inc-ua idCatIso ∙ sym (inc-ua f) ≡⟨ congL _∙_ inc-id ⟩
    refl ∙ sym (inc-ua f) ≡⟨ sym (lUnit (sym (inc-ua f))) ⟩
    sym (inc-ua f) ∎

  inc-pathToIso : (p : x ≡ y) → inc-ua (pathToIso p) ≡ cong inc p
  inc-pathToIso = J (λ y p → inc-ua (pathToIso p) ≡ cong inc p) (cong inc-ua pathToIso-refl ∙ inc-id)

  inc-surj : isSurjection inc
  inc-surj = GQ.isSurjective[] ⋆IsoC

  RezkHomSet : RezkOb → RezkOb → hSet ℓ'
  RezkHomSet =
    rec₂ isGroupoidHSet H-inc H-inc-ua H-ua-inc H-ua-inc-ua H-inc-sq H-sq-inc where

    H-inc : ob C → ob C → hSet ℓ'
    H-inc x y = C .Hom[_,_] x y , C .isSetHom

    H-inc-ua : ∀ {x y z} → IsoC y z → H-inc x y ≡ H-inc x z
    H-inc-ua f = TypeOfHLevel≡ 2 $ isoToPath λ where
      .Iso.fun → C._⋆ f .fst
      .Iso.inv → C._⋆ f .snd .inv
      .Iso.rightInv _ → C.⋆Assoc _ _ _ ∙∙ congR C._⋆_ (f .snd .sec) ∙∙ C.⋆IdR _
      .Iso.leftInv  _ → C.⋆Assoc _ _ _ ∙∙ congR C._⋆_ (f .snd .ret) ∙∙ C.⋆IdR _

    H-ua-inc : ∀ {x y z} → IsoC x y → H-inc x z ≡ H-inc y z
    H-ua-inc f = TypeOfHLevel≡ 2 $ isoToPath λ where
      .Iso.fun → f .snd .inv C.⋆_
      .Iso.inv → f .fst C.⋆_
      .Iso.rightInv _ → sym (C.⋆Assoc _ _ _) ∙∙ congL C._⋆_ (f .snd .sec) ∙∙ C.⋆IdL _
      .Iso.leftInv  _ → sym (C.⋆Assoc _ _ _) ∙∙ congL C._⋆_ (f .snd .ret) ∙∙ C.⋆IdL _

    typeSquare : ∀ {A B C D : Type ℓ''} {P : A ≡ B} {Q : C ≡ D} {R S}
               → (∀ x → transport S (transport P x) ≡ transport Q (transport R x))
               → Square P Q R S
    typeSquare h = compPath→Square $ isInjectiveTransport $ funExt λ x →
      transportComposite _ _ x ∙∙ sym (h x) ∙∙ sym (transportComposite _ _ x)

    H-ua-inc-ua : ∀ {x y z w} (g : IsoC z w) (f : IsoC x y)
                → Square (H-ua-inc g) (H-ua-inc g) (H-inc-ua f) (H-inc-ua f)
    H-ua-inc-ua g f = ΣSquareSet (λ _ → isProp→isSet isPropIsSet) $ typeSquare λ h →
      transport (cong fst (H-inc-ua f)) (transport (cong fst (H-ua-inc g)) h)
        ≡⟨ uaβ _ _ ⟩
      transport (cong fst (H-ua-inc g)) h C.⋆ f .fst
        ≡⟨ congL C._⋆_ (uaβ _ _) ⟩
      (g .snd .inv C.⋆ h) C.⋆ f .fst
        ≡⟨ C.⋆Assoc (g .snd .inv) h (f .fst) ⟩
      g .snd .inv C.⋆ (h C.⋆ f .fst)
        ≡⟨ congR C._⋆_ (sym (uaβ _ _)) ⟩
      g .snd .inv C.⋆ (transport (cong fst (H-inc-ua f)) h)
        ≡⟨ sym (uaβ _ _) ⟩
      transport (cong fst (H-ua-inc g)) (transport (cong fst (H-inc-ua f)) h) ∎

    H-inc-sq : ∀ {x y z w} (f : IsoC y z) (g : IsoC z w)
             → Square (H-inc-ua {x = x} f) (H-inc-ua (⋆Iso f g)) refl (H-inc-ua g)
    H-inc-sq f g = ΣSquareSet (λ _ → isProp→isSet isPropIsSet) $ typeSquare λ h →
      transport (cong fst (H-inc-ua g)) (transport (cong fst (H-inc-ua f)) h)
        ≡⟨ uaβ _ _ ⟩
      transport (cong fst (H-inc-ua f)) h C.⋆ g .fst
        ≡⟨ congL C._⋆_ (uaβ _ _) ⟩
      (h C.⋆ f .fst) C.⋆ g .fst
        ≡⟨ C.⋆Assoc _ _ _ ⟩
      h C.⋆ (f .fst C.⋆ g .fst)
        ≡⟨ congL C._⋆_ (sym (transportRefl h)) ⟩
      transport refl h C.⋆ (f .fst C.⋆ g .fst)
        ≡⟨ sym (uaβ _ _) ⟩
      transport (cong fst (H-inc-ua (⋆Iso f g))) (transport refl h) ∎

    H-sq-inc : ∀ {x y z w} (f : IsoC x y) (g : IsoC y z)
             → Square (H-ua-inc {z = w} f) (H-ua-inc (⋆Iso f g)) refl (H-ua-inc g)
    H-sq-inc f g = ΣSquareSet (λ _ → isProp→isSet isPropIsSet) $ typeSquare λ h →
      transport (cong fst (H-ua-inc g)) (transport (cong fst (H-ua-inc f)) h)
        ≡⟨ uaβ _ _ ⟩
      g .snd .inv C.⋆ transport (cong fst (H-ua-inc f)) h
        ≡⟨ congR C._⋆_ (uaβ _ _) ⟩
      g .snd .inv C.⋆ (f .snd .inv C.⋆ h)
        ≡⟨ sym (C.⋆Assoc _ _ _) ⟩
      (g .snd .inv C.⋆ f .snd .inv) C.⋆ h
        ≡⟨ congR C._⋆_ (sym (transportRefl h)) ⟩
      (g .snd .inv C.⋆ f .snd .inv) C.⋆ transport refl h
        ≡⟨ sym (uaβ _ _) ⟩
      transport (cong fst (H-ua-inc (⋆Iso f g))) (transport refl h) ∎

  RezkHom : RezkOb → RezkOb → Type ℓ'
  RezkHom x y = RezkHomSet x y .fst

  isSetRezkHom : ∀ x y → isSet (RezkHom x y)
  isSetRezkHom x y = RezkHomSet x y .snd

  private
    tr : {A : Type ℓ''} → transport refl ≡ idfun A
    tr = funExt transportRefl

  RezkId : ∀ x → RezkHom x x
  RezkId = elimSet (λ x → isSetRezkHom x x) (λ x → C.id) λ f → toPathP $
    subst2 RezkHom (inc-ua f) (inc-ua f) C.id
      ≡[ i ]⟨ tr i (tr i (tr i (tr i (f .snd .inv C.⋆ tr i (tr i (tr i (tr i C.id)) C.⋆ f .fst))))) ⟩
    f .snd .inv C.⋆ (C.id C.⋆ f .fst)
      ≡⟨ congR C._⋆_ (C.⋆IdL _) ⟩
    f .snd .inv C.⋆ f .fst
      ≡⟨ f .snd .sec ⟩
    C.id ∎

  Rezk⋆ : ∀ x y z → RezkHom x y → RezkHom y z → RezkHom x z
  Rezk⋆ = elimSet₃ (λ x y z → isSet→ (isSet→ (isSetRezkHom x z))) (λ x y z → C._⋆_)
    lem₁ lem₂ lem₃ where

    lem₁ : ∀ {x y z w} (f : Σ C.Hom[ z , w ] (isIso C))
         → PathP (λ i → RezkHom (inc x) (inc y) →
             RezkHom (inc y) (inc-ua f i) → RezkHom (inc x) (inc-ua f i)) C._⋆_ C._⋆_
    lem₁ e = funExt λ f → toPathP $ funExt λ g →
      transport refl ((f C.⋆ (transport refl g C.⋆ e .snd .inv)) C.⋆ e .fst)
        ≡⟨ transportRefl _ ⟩
      (f C.⋆ transport refl g C.⋆ e .snd .inv) C.⋆ e .fst
        ≡⟨ C.⋆Assoc _ _ _ ⟩
      f C.⋆ (transport refl g C.⋆ e .snd .inv) C.⋆ e .fst
        ≡⟨ congR C._⋆_ (
          (transport refl g C.⋆ e .snd .inv) C.⋆ e .fst
            ≡⟨ C.⋆Assoc _ _ _ ⟩
          transport refl g C.⋆ e. snd .inv C.⋆ e .fst
            ≡⟨ cong₂ C._⋆_ (transportRefl g) (e .snd .sec) ⟩
          g C.⋆ C.id
            ≡⟨ C.⋆IdR _ ⟩
          g ∎
        ) ⟩
      f C.⋆ g ∎

    lem₂ : ∀ {x y z w} (f : Σ C.Hom[ y , z ] (isIso C))
         → PathP (λ i → RezkHom (inc x) (inc-ua f i) →
             RezkHom (inc-ua f i) (inc w) → RezkHom (inc x) (inc w)) C._⋆_ C._⋆_
    lem₂ e = toPathP $ funExt₂ λ f g →
      tr i0 ((tr i0 f C.⋆ e .snd .inv) C.⋆ e .fst C.⋆ tr i0 g)
        ≡[ i ]⟨ tr i ((tr i f C.⋆ e .snd .inv) C.⋆ e .fst C.⋆ tr i g) ⟩
      (f C.⋆ e .snd .inv) C.⋆ e .fst C.⋆ g
        ≡⟨ C.⋆Assoc _ _ _ ⟩
      f C.⋆ (e .snd .inv C.⋆ e .fst C.⋆ g)
        ≡⟨ congR C._⋆_ (sym (C.⋆Assoc _ _ _) ∙ congL C._⋆_ (e .snd .sec) ∙ C.⋆IdL _) ⟩
      f C.⋆ g ∎

    lem₃ : ∀ {x y z w} (f : Σ C.Hom[ x , y ] (isIso C))
         → PathP (λ i → RezkHom (inc-ua f i) (inc z) →
             RezkHom (inc z) (inc w) → RezkHom (inc-ua f i) (inc w)) C._⋆_ C._⋆_
    lem₃ e = toPathP $ funExt₂ λ f g →
      tr i0 (e .snd .inv C.⋆ (e .fst C.⋆ tr i0 f) C.⋆ tr i0 g)
        ≡[ i ]⟨ tr i (e .snd .inv C.⋆ (e .fst C.⋆ tr i f) C.⋆ tr i g) ⟩
      e .snd .inv C.⋆ (e .fst C.⋆ f) C.⋆ g
        ≡⟨ sym (C.⋆Assoc _ _ _) ⟩
      (e .snd .inv C.⋆ e .fst C.⋆ f) C.⋆ g
        ≡⟨ congL C._⋆_ (sym (C.⋆Assoc _ _ _) ∙ congL C._⋆_ (e .snd .sec) ∙ C.⋆IdL _) ⟩
      f C.⋆ g ∎

  Rezk⋆IdL : ∀ x y f → Rezk⋆ x x y (RezkId x) f ≡ f
  Rezk⋆IdL = elimProp₂ (λ x y → isPropΠ (λ _ → isSetRezkHom x y _ _)) λ x y → C.⋆IdL

  Rezk⋆IdR : ∀ x y f → Rezk⋆ x y y f (RezkId y) ≡ f
  Rezk⋆IdR = elimProp₂ (λ x y → isPropΠ (λ _ → isSetRezkHom x y _ _)) λ x y → C.⋆IdR

  Rezk⋆Assoc : ∀ x y z w f g h
             → Rezk⋆ x z w (Rezk⋆ x y z f g) h ≡ Rezk⋆ x y w f (Rezk⋆ y z w g h)
  Rezk⋆Assoc = elimProp₂ (λ x y → isPropΠ5 λ z w _ _ _ → isSetRezkHom x w _ _) λ x y →
               elimProp₂ (λ z w → isPropΠ3 λ _ _ _ → isSetRezkHom (inc x) w _ _) λ z w → C.⋆Assoc

  Rezk : Category (ℓ-max ℓ ℓ') ℓ'
  Rezk .ob = RezkOb
  Rezk .Hom[_,_] = RezkHom
  Rezk .id {x} = RezkId x
  Rezk ._⋆_ {x} {y} {z} = Rezk⋆ x y z
  Rezk .⋆IdL {x} {y} = Rezk⋆IdL x y
  Rezk .⋆IdR {x} {y} = Rezk⋆IdR x y
  Rezk .⋆Assoc {x} {y} {z} {w} = Rezk⋆Assoc x y z w
  Rezk .isSetHom {x} {y} = isSetRezkHom x y

  RezkIso→Iso : ∀ {x y} → CatIso Rezk (inc x) (inc y) → IsoC x y
  RezkIso→Iso (f , isiso g s r) = (f , isiso g s r)

  Iso→RezkIso : ∀ {x y} → IsoC x y → CatIso Rezk (inc x) (inc y)
  Iso→RezkIso (f , isiso g s r) = (f , isiso g s r)

  RezkIsoToPath : ∀ x y → CatIso Rezk x y → x ≡ y
  RezkIsoToPath = elimSet₂ (λ x y → isSet→ (squash x y)) R-inc R-ua₁ R-ua₂ where

    R-inc = λ x y f → inc-ua (RezkIso→Iso f)

    R-ua₁ : {x y z : C.ob} (f : Σ C.Hom[ y , z ] (isIso C))
          → PathP (λ i → CatIso Rezk (inc x) (inc-ua f i) → inc x ≡ inc-ua f i)
              (R-inc x y) (R-inc x z)
    R-ua₁ e = toPathP $ funExt λ f → let f' = RezkIso→Iso f in
      subst2 _≡_ refl (inc-ua e) (inc-ua _)
        ≡⟨ cong (subst2 _≡_ refl (inc-ua e) ∘ inc-ua) (
          CatIso≡ _ _ (congL C._⋆_ (transportRefl _))
        ) ⟩
      subst2 _≡_ refl (inc-ua e) (inc-ua (⋆Iso f' (invIso e)))
        ≡⟨ fromPathP (compPath-filler (inc-ua (⋆Iso f' (invIso e))) (inc-ua e)) ⟩
      inc-ua (⋆Iso f' (invIso e)) ∙ inc-ua e
        ≡⟨ sym (inc-⋆ (⋆Iso f' (invIso e)) e) ⟩
      inc-ua (⋆Iso (⋆Iso f' (invIso e)) e)
        ≡⟨ cong inc-ua (CatIso≡ _ _ (C.⋆Assoc _ _ _ ∙ congR C._⋆_ (e .snd .sec) ∙ C.⋆IdR _)) ⟩
      inc-ua f' ∎

    R-ua₂ : {x y z : C.ob} (f : Σ C.Hom[ x , y ] (isIso C))
          → PathP (λ i → CatIso Rezk (inc-ua f i) (inc z) → inc-ua f i ≡ inc z)
              (R-inc x z) (R-inc y z)
    R-ua₂ e = toPathP $ funExt λ f → let f' = RezkIso→Iso f in
      subst2 _≡_ (inc-ua e) refl (inc-ua _)
        ≡⟨ cong (subst2 _≡_ (inc-ua e) refl ∘ inc-ua) (CatIso≡ _ _ (congR C._⋆_ (transportRefl _))) ⟩
      subst2 _≡_ (inc-ua e) refl (inc-ua (⋆Iso e f'))
        ≡⟨ fromPathP (compPath-filler' (sym (inc-ua e)) (inc-ua (⋆Iso e f'))) ⟩
      sym (inc-ua e) ∙ inc-ua (⋆Iso e f')
        ≡⟨ congR _∙_ (inc-⋆ e f') ⟩
      sym (inc-ua e) ∙ (inc-ua e ∙ inc-ua f')
        ≡⟨ compPathl-cancel (sym (inc-ua e)) (inc-ua f') ⟩
      inc-ua f' ∎

  RezkIsoToPathId : ∀ x → RezkIsoToPath x x idCatIso ≡ refl
  RezkIsoToPathId = elimProp (λ x → squash x x _ _) (λ x → inc-id)

  RezkIsoToPathη : ∀ x y p → RezkIsoToPath x y (pathToIso p) ≡ p
  RezkIsoToPathη x = J> cong (RezkIsoToPath x x) pathToIso-refl ∙ RezkIsoToPathId x

  RezkIsoToPathβ : ∀ x y f → pathToIso (RezkIsoToPath x y f) ≡ f
  RezkIsoToPathβ = elimProp₂ (λ x y → isPropΠ λ _ → isSet-CatIso x y _ _) λ x y f →
    CatIso≡ _ _ $ transportRefl _ ∙ C.⋆IdL _

  isUnivalentRezk : isUnivalent Rezk
  isUnivalentRezk .univ x y = isoToIsEquiv $
    iso pathToIso (RezkIsoToPath x y) (RezkIsoToPathβ x y) (RezkIsoToPathη x y)

  →Rezk : Functor C Rezk
  →Rezk .F-ob = inc
  →Rezk .F-hom = idfun _
  →Rezk .F-id = refl
  →Rezk .F-seq f g = refl

  →RezkFF : isFullyFaithful →Rezk
  →RezkFF x y = idIsEquiv _

  →RezkSurj : isEssentiallySurj →Rezk
  →RezkSurj = elimProp (λ x → isPropPropTrunc) λ x → ∣ x , idCatIso ∣₁

  isWkEquiv→Rezk : isWeakEquivalence →Rezk
  isWkEquiv→Rezk .fullfaith = →RezkFF
  isWkEquiv→Rezk .esssurj = →RezkSurj

  isRezkCompletion→Rezk : isRezkCompletion →Rezk
  isRezkCompletion→Rezk = makeIsRezkCompletion isUnivalentRezk isWkEquiv→Rezk

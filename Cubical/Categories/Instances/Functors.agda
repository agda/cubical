{-# OPTIONS --safe #-}

{-
   Category whose objects are functors and morphisms are natural transformations.

   Includes the following
   - isos in FUNCTOR are precisely the pointwise isos
   - FUNCTOR C D is univalent when D is
   - Isomorphism of functors currying

-}

module Cubical.Categories.Instances.Functors where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Morphism
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.NaturalTransformation.Properties
open import Cubical.Foundations.Function renaming (_∘_ to _∘→_)

private
  variable
    ℓC ℓC' ℓD ℓD' ℓE ℓE' : Level

module _ (C : Category ℓC ℓC') (D : Category ℓD ℓD') where
  open Category
  open NatTrans
  open Functor

  FUNCTOR : Category (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) (ℓ-max (ℓ-max ℓC ℓC') ℓD')
  ob FUNCTOR           = Functor C D
  Hom[_,_] FUNCTOR     = NatTrans
  id FUNCTOR {F}       = idTrans F
  _⋆_ FUNCTOR          = seqTrans
  ⋆IdL FUNCTOR α       = makeNatTransPath λ i x → D .⋆IdL (α .N-ob x) i
  ⋆IdR FUNCTOR α       = makeNatTransPath λ i x → D .⋆IdR (α .N-ob x) i
  ⋆Assoc FUNCTOR α β γ = makeNatTransPath λ i x → D .⋆Assoc (α .N-ob x) (β .N-ob x) (γ .N-ob x) i
  isSetHom FUNCTOR     = isSetNatTrans

  open isIsoC renaming (inv to invC)
  -- componentwise iso is an iso in Functor
  FUNCTORIso : ∀ {F G : Functor C D} (α : F ⇒ G)
             → (∀ (c : C .ob) → isIsoC D (α ⟦ c ⟧))
             → isIsoC FUNCTOR α
  FUNCTORIso α is .invC .N-ob c = (is c) .invC
  FUNCTORIso {F} {G} α is .invC .N-hom {c} {d} f
    = invMoveL areInv-αc
               ( α ⟦ c ⟧ ⋆⟨ D ⟩ (G ⟪ f ⟫ ⋆⟨ D ⟩ is d .invC)
               ≡⟨ sym (D .⋆Assoc _ _ _) ⟩
                 (α ⟦ c ⟧ ⋆⟨ D ⟩ G ⟪ f ⟫) ⋆⟨ D ⟩ is d .invC
               ≡⟨ sym (invMoveR areInv-αd (α .N-hom f)) ⟩
                 F ⟪ f ⟫
               ∎ )
    where
      areInv-αc : areInv _ (α ⟦ c ⟧) ((is c) .invC)
      areInv-αc = isIso→areInv (is c)

      areInv-αd : areInv _ (α ⟦ d ⟧) ((is d) .invC)
      areInv-αd = isIso→areInv (is d)
  FUNCTORIso α is .sec = makeNatTransPath (funExt (λ c → (is c) .sec))
  FUNCTORIso α is .ret = makeNatTransPath (funExt (λ c → (is c) .ret))

  -- iso is componentwise iso in Functor
  FUNCTORIso' : ∀ {F G : Functor C D} (α : F ⇒ G)
             → isIsoC FUNCTOR α
             → ((c : C .ob) → isIsoC D (α ⟦ c ⟧))
  FUNCTORIso' α isom c .invC = isom .invC .N-ob c
  FUNCTORIso' α isom c .sec i = isom .sec i .N-ob c
  FUNCTORIso' α isom c .ret i = isom .ret i .N-ob c

  open Iso
  open NatIso

  FUNCTORIso→NatIso : {F G : Functor C D} → CatIso FUNCTOR F G → NatIso F G
  FUNCTORIso→NatIso α .trans = α .fst
  FUNCTORIso→NatIso α .nIso = FUNCTORIso' _ (α .snd)

  NatIso→FUNCTORIso : {F G : Functor C D} → NatIso F G → CatIso FUNCTOR F G
  NatIso→FUNCTORIso α = α .trans , FUNCTORIso _ (α .nIso)

  Path→FUNCTORIso→NatIso : {F G : Functor C D} → (p : F ≡ G) → pathToNatIso p ≡ FUNCTORIso→NatIso (pathToIso p)
  Path→FUNCTORIso→NatIso {F = F} p = J (λ _ p → pathToNatIso p ≡ FUNCTORIso→NatIso (pathToIso p)) (NatIso≡ refl-helper) p
    where
    refl-helper : _
    refl-helper i x = ((λ i → pathToIso-refl {C = D} {x = F .F-ob x} i .fst)
      ∙ (λ i → pathToIso-refl {C = FUNCTOR} {x = F} (~ i) .fst .N-ob x)) i

  Iso-FUNCTORIso-NatIso : {F G : Functor C D} → Iso (CatIso FUNCTOR F G) (NatIso F G)
  Iso-FUNCTORIso-NatIso .fun = FUNCTORIso→NatIso
  Iso-FUNCTORIso-NatIso .inv = NatIso→FUNCTORIso
  Iso-FUNCTORIso-NatIso .rightInv α i .trans = α .trans
  Iso-FUNCTORIso-NatIso .rightInv α i .nIso =
    isProp→PathP (λ i → isPropΠ (λ _ → isPropIsIso _)) (FUNCTORIso' (α .trans) (FUNCTORIso _ (α .nIso))) (α .nIso) i
  Iso-FUNCTORIso-NatIso .leftInv α i .fst = α .fst
  Iso-FUNCTORIso-NatIso .leftInv α i .snd =
    isProp→PathP (λ i → isPropIsIso _) (FUNCTORIso _ (FUNCTORIso' _ (α .snd))) (α .snd) i

  FUNCTORIso≃NatIso : {F G : Functor C D} → CatIso FUNCTOR F G ≃ NatIso F G
  FUNCTORIso≃NatIso = isoToEquiv Iso-FUNCTORIso-NatIso


  -- Functor Category is Univalent if the Target Category is Univalent

  open isUnivalent

  isUnivalentFUNCTOR : isUnivalent D → isUnivalent FUNCTOR
  isUnivalentFUNCTOR isUnivD .univ _ _ =
    isEquiv[equivFunA≃B∘f]→isEquiv[f] _ FUNCTORIso≃NatIso
      (subst isEquiv (λ i p → Path→FUNCTORIso→NatIso p i) (Path≃NatIso isUnivD .snd))

  appF : Functor (FUNCTOR ×C C) D
  appF .F-ob (F , c) = F ⟅ c ⟆
  appF .F-hom {F , c} {G , d} (α , f) = α .N-ob d ∘⟨ D ⟩ F .F-hom f
  appF .F-id {F , c} =
    D .id ∘⟨ D ⟩ F .F-hom (C .id) ≡⟨ D .⋆IdR (F .F-hom (C .id)) ⟩
    F .F-hom (C .id) ≡⟨ F .F-id ⟩
    D .id ∎
  appF .F-seq {F , c}{G , d}{H , e} (α , f) (β , g ) =
    (β .N-ob e ∘⟨ D ⟩ α .N-ob e) ∘⟨ D ⟩ F .F-hom (g ∘⟨ C ⟩ f)
      ≡⟨ (λ i → (β .N-ob e ∘⟨ D ⟩ α .N-ob e) ∘⟨ D ⟩ F .F-seq f g i) ⟩
    (β .N-ob e ∘⟨ D ⟩ α .N-ob e) ∘⟨ D ⟩ (F .F-hom g ∘⟨ D ⟩ F .F-hom f)
      ≡⟨ sym (D .⋆Assoc _ _ _) ⟩
    β .N-ob e ∘⟨ D ⟩ (α .N-ob e ∘⟨ D ⟩ (F .F-hom g ∘⟨ D ⟩ F .F-hom f))
      ≡⟨ (λ i → β .N-ob e
                ∘⟨ D ⟩ D .⋆Assoc (F .F-hom f) (F .F-hom g) (α .N-ob e) i) ⟩
    β .N-ob e ∘⟨ D ⟩ ((α .N-ob e ∘⟨ D ⟩ F .F-hom g) ∘⟨ D ⟩ F .F-hom f)
      ≡⟨ (λ i → β .N-ob e ∘⟨ D ⟩ α .N-hom g i ∘⟨ D ⟩ F .F-hom f) ⟩
    β .N-ob e ∘⟨ D ⟩ ((G .F-hom g ∘⟨ D ⟩ α .N-ob d) ∘⟨ D ⟩ F .F-hom f)
      ≡⟨ (λ i → β .N-ob e
                ∘⟨ D ⟩ D .⋆Assoc (F .F-hom f) (α .N-ob d) (G .F-hom g) (~ i) ) ⟩
    β .N-ob e ∘⟨ D ⟩ (G .F-hom g ∘⟨ D ⟩ (α .N-ob d ∘⟨ D ⟩ F .F-hom f))
      ≡⟨ D .⋆Assoc _ _ _ ⟩
    (β .N-ob e ∘⟨ D ⟩ G .F-hom g) ∘⟨ D ⟩ (α .N-ob d ∘⟨ D ⟩ F .F-hom f) ∎
  module _ (E : Category ℓE ℓE') where
    λF : Functor (E ×C C) D → Functor E FUNCTOR
    λF F .F-ob e .F-ob c = F ⟅ e , c ⟆
    λF F .F-ob e .F-hom f = F ⟪ (E .id) , f ⟫
    λF F .F-ob e .F-id = F .F-id
    λF F .F-ob e .F-seq f g =
      F ⟪ E .id , g ∘⟨ C ⟩ f ⟫
        ≡⟨ (λ i → F ⟪ (E .⋆IdL (E .id) (~ i)) , (g ∘⟨ C ⟩ f) ⟫) ⟩
      (F ⟪ (E .id ∘⟨ E ⟩ E .id) , g ∘⟨ C ⟩ f ⟫)
        ≡⟨ F .F-seq (E .id , f) (E .id , g) ⟩
      (F ⟪ E .id , g ⟫ ∘⟨ D ⟩ F ⟪ E .id , f ⟫) ∎
    λF F .F-hom h .N-ob c = F ⟪ h , (C .id) ⟫
    λF F .F-hom h .N-hom f =
      F ⟪ h , C .id ⟫ ∘⟨ D ⟩ F ⟪ E .id , f ⟫ ≡⟨ sym (F .F-seq _ _) ⟩
      F ⟪ h ∘⟨ E ⟩ E .id , C .id ∘⟨ C ⟩ f ⟫
        ≡⟨ (λ i → F ⟪ E .⋆IdL h i , C .⋆IdR f i  ⟫) ⟩
      F ⟪ h , f ⟫ ≡⟨ (λ i → F ⟪ (E .⋆IdR h (~ i)) , (C .⋆IdL f (~ i)) ⟫) ⟩
      F ⟪ E .id ∘⟨ E ⟩ h , f ∘⟨ C ⟩ C .id ⟫ ≡⟨ F .F-seq _ _ ⟩
      F ⟪ E .id , f ⟫ ∘⟨ D ⟩ F ⟪ h , C .id ⟫ ∎
    λF F .F-id = makeNatTransPath (funExt λ c → F .F-id)
    λF F .F-seq f g = makeNatTransPath (funExt lem) where
      lem : (c : C .ob) →
            F ⟪ g ∘⟨ E ⟩ f , C .id ⟫ ≡
            F ⟪ g , C .id ⟫ ∘⟨ D ⟩ F ⟪ f , C .id ⟫
      lem c =
        F ⟪ g ∘⟨ E ⟩ f , C .id ⟫
          ≡⟨ (λ i → F ⟪ (g ∘⟨ E ⟩ f) , (C .⋆IdR (C .id) (~ i)) ⟫) ⟩
        F ⟪ g ∘⟨ E ⟩ f , C .id ∘⟨ C ⟩ C .id ⟫
          ≡⟨ F .F-seq (f , C .id) (g , C .id) ⟩
        (F ⟪ g , C .id ⟫) ∘⟨ D ⟩ (F ⟪ f , C .id ⟫) ∎


    λF⁻ : Functor E FUNCTOR → Functor (E ×C C) D
    F-ob (λF⁻ a) = uncurry (F-ob ∘→ F-ob a)
    F-hom (λF⁻ a) _ = N-ob (F-hom a _) _ ∘⟨ D ⟩ (F-hom (F-ob a _)) _
    F-id (λF⁻ a) = cong₂ (seq' D) (F-id (F-ob a _))
        (cong (flip N-ob _) (F-id a)) ∙ D .⋆IdL _
    F-seq (λF⁻ a) _ (eG , cG) =
     cong₂ (seq' D) (F-seq (F-ob a _) _ _) (cong (flip N-ob _)
           (F-seq a _ _))
          ∙ AssocCong₂⋆R {C = D} _
              (N-hom ((F-hom a _) ●ᵛ (F-hom a _)) _ ∙
                (⋆Assoc D _ _ _) ∙
                  cong (seq' D _) (sym (N-hom (F-hom a eG) cG)))

    isoλF : Iso (Functor (E ×C C) D) (Functor E FUNCTOR)
    fun isoλF = λF
    inv isoλF = λF⁻
    rightInv isoλF b = Functor≡ (λ _ → Functor≡ (λ _ → refl)
      λ _ → cong (seq' D _) (congS (flip N-ob _) (F-id b)) ∙ D .⋆IdR _)
      λ _ → toPathP (makeNatTransPath (transportRefl _ ∙
        funExt λ _ → cong (flip (seq' D) _) (F-id (F-ob b _)) ∙ D .⋆IdL _))
    leftInv isoλF a = Functor≡ (λ _ → refl) λ _ → sym (F-seq a _ _)
          ∙ cong (F-hom a) (cong₂ _,_ (E .⋆IdL _) (C .⋆IdR _))

{-# OPTIONS --safe #-}

module Cubical.Categories.Instances.Functors where

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.NaturalTransformation.Properties
open import Cubical.Categories.Morphism
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

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

{-# OPTIONS --safe #-}

module Cubical.Categories.Functor.ComposeProperty where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as Prop

open import Cubical.Categories.Category
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.Equivalence.WeakEquivalence

open import Cubical.Categories.Instances.Functors


-- Composition induced by special functors

module _ {ℓC ℓC' ℓD ℓD' ℓE ℓE'}
  {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} (E : Category ℓE ℓE')
  (F : Functor C D)
  where

  open Category
  open Functor
  open NatTrans
  open isIso


  isEssSurj→isFaithfulPrecomp : isEssentiallySurj F → isFaithful (precomposeF E F)
  isEssSurj→isFaithfulPrecomp surj A B α β p =
    makeNatTransPath
      (λ i x → Prop.rec (E .isSetHom _ _)
      (λ (c , f) →
          ⋆InvLMove (F-Iso {F = A} f) (α .N-hom (f .fst))
        ∙ (λ i → F-Iso {F = A} f .snd .inv ⋆⟨ E ⟩ (p i .N-ob c ⋆⟨ E ⟩ B .F-hom (f .fst)))
        ∙ sym (⋆InvLMove (F-Iso {F = A} f) (β .N-hom (f .fst))))
      (surj x) i)


  isEssSurj+Full→isFullPrecomp : isEssentiallySurj F → isFull F → isFull (precomposeF E F)
  isEssSurj+Full→isFullPrecomp surj full A B α = ∣ ext , ext≡ ∣₁
    where
    Mor : (d : D .ob) → Type _
    Mor d =
      Σ[ g ∈ E [ A .F-ob d , B .F-ob d ] ]
        ((c : C .ob)(f : CatIso D (F .F-ob c) d)
        → α .N-ob c ≡ A .F-hom (f .fst) ⋆⟨ E ⟩ g ⋆⟨ E ⟩ B .F-hom (f .snd .inv))

    isPropMor : (d : D .ob) → isProp (Mor d)
    isPropMor d x y = Σ≡Prop (λ _ → isPropΠ2 (λ _ _ → E .isSetHom _ _)) path
      where
      path : x .fst ≡ y .fst
      path = Prop.rec (E .isSetHom _ _)
        (λ (c , f) →
          ⋆CancelL (F-Iso {F = A} f) (⋆CancelR (invIso (F-Iso {F = B} f))
            (sym (x .snd c f) ∙ y .snd c f)))
        (surj d)

    isContrMor : (d : D .ob) → isContr (Mor d)
    isContrMor d = inhProp→isContr inhab (isPropMor d)
      where
      inhab : Mor d
      inhab = Prop.rec (isPropMor d)
        (λ (a , h) →
          A .F-hom (h .snd .inv) ⋆⟨ E ⟩ α .N-ob a ⋆⟨ E ⟩ B .F-hom (h .fst) ,
          λ c f →
            Prop.rec (E .isSetHom _ _)
            (λ (k , p) →
              let isom-path = subst-filler (isIso D) (sym p) (⋆Iso f (invIso h) .snd) in
                ⋆InvRMove (F-Iso {F = B} (_ , isom-path i1)) (sym (α .N-hom k))
              ∙ (λ i → A .F-hom (p i) ⋆⟨ E ⟩ α .N-ob a ⋆⟨ E ⟩ F-Iso {F = B} (p i , isom-path (~ i)) .snd .inv)
              ∙ (λ i → A .F-seq (f .fst) (h .snd .inv) i ⋆⟨ E ⟩ α .N-ob a ⋆⟨ E ⟩ F-Iso-Pres⋆ {F = B} h (invIso f) i .fst)
              ∙ sym (E .⋆Assoc _ _ _)
              ∙ cong (λ x → x ⋆⟨ E ⟩ _ ⋆⟨ E ⟩ _) (E .⋆Assoc _ _ _)
              ∙ cong (λ x → x ⋆⟨ E ⟩ _) (E .⋆Assoc _ _ _))
            (full _ _ (f .fst ⋆⟨ D ⟩ h .snd .inv)))
        (surj d)

    mor-eq : (d : D .ob)(c : C .ob)(f : CatIso D (F .F-ob c) d)
      → isContrMor d .fst .fst ≡ A .F-hom (f .snd .inv) ⋆⟨ E ⟩ α .N-ob c ⋆⟨ E ⟩ B .F-hom (f .fst)
    mor-eq d c f =
        ⋆InvLMove (F-Iso {F = A} f) (⋆InvRMove (invIso (F-Iso {F = B} f)) (sym (isContrMor d .fst .snd c f)))
      ∙ sym (E .⋆Assoc _ _ _)

    F-seq3 : (F : Functor D E) {x y z w : D .ob}
      → {f : D [ x , y ]}{g : D [ y , z ]}{h : D [ z , w ]}
      → F .F-hom (f ⋆⟨ D ⟩ g ⋆⟨ D ⟩ h) ≡ F .F-hom f ⋆⟨ E ⟩ F .F-hom g ⋆⟨ E ⟩ F .F-hom h
    F-seq3 F = F .F-seq _ _ ∙ cong (λ x → x ⋆⟨ E ⟩ _) (F .F-seq _ _)

    ext : NatTrans A B
    ext .N-ob d = isContrMor d .fst .fst
    ext .N-hom {x = d} {y = d'} f = Prop.rec2 (E .isSetHom _ _)
        (λ (c , h) (c' , h') → Prop.rec (E .isSetHom _ _)
        (λ (k , p) →
            (λ i → A .F-hom f ⋆⟨ E ⟩ mor-eq d' c' h' i)
          ∙ cong (λ x → A .F-hom f ⋆⟨ E ⟩ x) (E .⋆Assoc _ _ _)
          ∙ sym (E .⋆Assoc _ _ _) ∙ sym (E .⋆Assoc _ _ _)
          ∙ cong (λ x → x ⋆⟨ E ⟩ _ ⋆⟨ E ⟩ _) (sym (E .⋆IdL _))
          ∙ cong (λ x → x ⋆⟨ E ⟩ _ ⋆⟨ E ⟩ _ ⋆⟨ E ⟩ _) (sym (F-Iso {F = A} h .snd .sec))
          ∙ cong (λ x → x ⋆⟨ E ⟩ _ ⋆⟨ E ⟩ _) (E .⋆Assoc _ _ _)
          ∙ cong (λ x → _ ⋆⟨ E ⟩ x ⋆⟨ E ⟩ _ ⋆⟨ E ⟩ _) (sym (E .⋆Assoc _ _ _))
          ∙ cong (λ x → _ ⋆⟨ E ⟩ x ⋆⟨ E ⟩ _ ⋆⟨ E ⟩ _) (sym (F-seq3 A))
          ∙ cong (λ x → A .F-hom (invIso h .fst) ⋆⟨ E ⟩ x ⋆⟨ E ⟩ _ ⋆⟨ E ⟩ _) (sym (cong (A .F-hom) p))
          ∙ cong (λ x → x ⋆⟨ E ⟩ _) (E .⋆Assoc _ _ _)
          ∙ cong (λ x → _ ⋆⟨ E ⟩ x ⋆⟨ E ⟩ _) (α .N-hom k)
          ∙ cong (λ x → x ⋆⟨ E ⟩ _) (sym (E .⋆Assoc _ _ _))
          ∙ E .⋆Assoc _ _ _
          ∙ cong (λ x → _ ⋆⟨ E ⟩ _ ⋆⟨ E ⟩ (x ⋆⟨ E ⟩ B .F-hom (h' .fst))) (cong (B .F-hom) p)
          ∙ cong (λ x → _ ⋆⟨ E ⟩ _ ⋆⟨ E ⟩ (x ⋆⟨ E ⟩ B .F-hom (h' .fst))) (F-seq3 B)
          ∙ cong (λ x → _ ⋆⟨ E ⟩ _ ⋆⟨ E ⟩ x) (E .⋆Assoc _ _ _)
          ∙ cong (λ x → _ ⋆⟨ E ⟩ _ ⋆⟨ E ⟩ (_ ⋆⟨ E ⟩ _ ⋆⟨ E ⟩ x)) (F-Iso {F = B} h' .snd .sec)
          ∙ cong (λ x → _ ⋆⟨ E ⟩ _ ⋆⟨ E ⟩ x) (E .⋆IdR _)
          ∙ sym (E .⋆Assoc _ _ _)
          ∙ (λ i → mor-eq d c h (~ i) ⋆⟨ E ⟩ B .F-hom f))
        (full _ _ (h .fst ⋆⟨ D ⟩ f ⋆⟨ D ⟩ h' .snd .inv)))
        (surj d) (surj d')

    ext≡ : precomposeF E F .F-hom ext ≡ α
    ext≡ = makeNatTransPath (λ i c →
        (mor-eq _ c idCatIso
      ∙ (λ i → A .F-id i ⋆⟨ E ⟩ α .N-ob c ⋆⟨ E ⟩ B .F-id i)
      ∙ E .⋆IdR _ ∙ E .⋆IdL _) i)


    isEssSurj+Full→isFullyFaithfulPrecomp : isEssentiallySurj F → isFull F → isFullyFaithful (precomposeF E F)
    isEssSurj+Full→isFullyFaithfulPrecomp surj full =
      isFull+Faithful→isFullyFaithful {F = precomposeF E F}
        (isEssSurj+Full→isFullPrecomp surj full) (isEssSurj→isFaithfulPrecomp surj)


module _ {ℓC ℓC' ℓD ℓD' ℓE ℓE'}
  {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  {E : Category ℓE ℓE'} (isUnivE : isUnivalent E)
  (F : Functor C D)
  where

  open Category
  open Functor
  open NatTrans
  open isIso
  open isWeakEquivalence
  open isUnivalent isUnivE

  isWeakEquiv→isEssSurjPrecomp : isWeakEquivalence F → isEssentiallySurj (precomposeF E F)
  isWeakEquiv→isEssSurjPrecomp w-equiv G = {!!}
    where
    Obj : (d : D .ob) → Type _
    Obj d = Σ[ e ∈ E .ob ]
      Σ[ k ∈ ((c : C .ob)(h : CatIso D (F .F-ob c) d) → CatIso E (G .F-ob c) e) ]
        ((c c' : C .ob)(h : CatIso D (F .F-ob c) d)(h' : CatIso D (F .F-ob c') d)
          → (f : C [ c , c' ])
          → F .F-hom f ⋆⟨ D ⟩ h' .fst ≡ h .fst
          → G .F-hom f ⋆⟨ E ⟩ k c' h' .fst ≡ k c h .fst)

    module _ (d : D .ob)(c₀ : C .ob)(h₀ : CatIso D (F .F-ob c₀) d) where

      g : (c : C .ob)(h : CatIso D (F .F-ob c) d) → CatIso C c c₀
      g c h = liftIso {F = F} (w-equiv .fullfaith) (⋆Iso h (invIso h₀))

      g-eq : ∀ c h → F .F-hom (g c h .fst) ⋆⟨ D ⟩ h₀ .fst ≡ h .fst
      g-eq c h =
          cong (λ x → x ⋆⟨ D ⟩ _) (cong fst (liftIso≡ {F = F} (w-equiv .fullfaith) (⋆Iso h (invIso h₀))))
        ∙ D .⋆Assoc _ _ _
        ∙ cong (λ x → _ ⋆⟨ D ⟩ x) (h₀ .snd .sec)
        ∙ D .⋆IdR _

      isContrObj' : isContr (Obj d)
      isContrObj' .fst .fst = G .F-ob c₀
      isContrObj' .fst .snd .fst c h = F-Iso {F = G} (g c h)
      isContrObj' .fst .snd .snd c c' h h' f p = sym (G .F-seq _ _) ∙ cong (G .F-hom) g-path
        where
        g-path : f ⋆⟨ C ⟩ g c' h' .fst ≡ g c h .fst
        g-path = isFullyFaithful→Faithful {F = F} (w-equiv .fullfaith) _ _ _ _
           (F .F-seq _ _
          ∙ cong (λ x → _ ⋆⟨ D ⟩ x) (cong fst (liftIso≡ {F = F} (w-equiv .fullfaith) (⋆Iso h' (invIso h₀))))
          ∙ sym (D .⋆Assoc _ _ _)
          ∙ cong (λ x → x ⋆⟨ D ⟩ invIso h₀ .fst) p
          ∙ cong fst (sym (liftIso≡ {F = F} (w-equiv .fullfaith) (⋆Iso h (invIso h₀)))))
      isContrObj' .snd (e , k , coh) i .fst = CatIsoToPath (k c₀ h₀) i
      isContrObj' .snd (e , k , coh) i .snd .fst c h =
        let isom₀ = F-Iso {F = G} (g c h) in
        hcomp (λ j → λ
          { (i = i0) → isom₀
          ; (i = i1) → CatIso≡ (⋆Iso isom₀ (k c₀ h₀)) (k c h) (coh c c₀ h h₀ (g c h .fst) (g-eq c h)) j })
        (transportIsoToPathIso isUnivE isom₀ _ i)
      isContrObj' .snd x@(e , k , coh) i .snd .snd =
        isProp→PathP (λ i → isPropΠ6 (λ c c' h h' f _ →
          E .isSetHom
            (G .F-hom f ⋆⟨ E ⟩ isContrObj' .snd x i .snd .fst c' h' .fst)
            (isContrObj' .snd x i .snd .fst c h .fst)))
        (isContrObj' .fst .snd .snd) coh i

    isContrObj : (d : D .ob) → isContr (Obj d)
    isContrObj d = Prop.rec isPropIsContr (λ (c , h) → isContrObj' d c h) (w-equiv .esssurj d)

    Ext-ob : D .ob → E .ob
    Ext-ob d = isContrObj d .fst .fst

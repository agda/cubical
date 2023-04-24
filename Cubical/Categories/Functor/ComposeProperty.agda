{-# OPTIONS --safe --lossy-unification #-}

module Cubical.Categories.Functor.ComposeProperty where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv

open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as Prop

open import Cubical.Categories.Category
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.Equivalence
open import Cubical.Categories.Equivalence.WeakEquivalence

open import Cubical.Categories.Instances.Functors


-- Composition by functor with special properties

module _ {ℓC ℓC' ℓD ℓD' ℓE ℓE'}
  {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} (E : Category ℓE ℓE')
  (F : Functor C D)
  where

  open Category
  open Functor
  open NatTrans
  open isIso


  -- If F is essential surjective, (- ∘ F) is faithful.

  isEssSurj→isFaithfulPrecomp : isEssentiallySurj F → isFaithful (precomposeF E F)
  isEssSurj→isFaithfulPrecomp surj A B α β p =
    makeNatTransPath
      (λ i x → Prop.rec (E .isSetHom _ _)
      (λ (c , f) →
          ⋆InvLMove (F-Iso {F = A} f) (α .N-hom (f .fst))
        ∙ (λ i → F-Iso {F = A} f .snd .inv ⋆⟨ E ⟩ (p i .N-ob c ⋆⟨ E ⟩ B .F-hom (f .fst)))
        ∙ sym (⋆InvLMove (F-Iso {F = A} f) (β .N-hom (f .fst))))
      (surj x) i)


  -- If F is essential surjective and full, (- ∘ F) is full.

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


  -- As a corollary, if F is essential surjective and full, (- ∘ F) is fully faithfull.

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


  -- If F is weak equivalence and the target category is univalent, (- ∘ F) is essentially surjective.

  isWeakEquiv→isEssSurjPrecomp : isWeakEquivalence F → isEssentiallySurj (precomposeF E F)
  isWeakEquiv→isEssSurjPrecomp w-equiv G = ∣ Ext , Ext≃ ∣₁
    where
    Obj : (d : D .ob) → Type _
    Obj d = Σ[ e ∈ E .ob ]
      Σ[ k ∈ ((c : C .ob)(h : CatIso D (F .F-ob c) d) → CatIso E (G .F-ob c) e) ]
        ((c c' : C .ob)(h : CatIso D (F .F-ob c) d)(h' : CatIso D (F .F-ob c') d)
          → (f : C [ c , c' ])
          → F .F-hom f ⋆⟨ D ⟩ h' .fst ≡ h .fst
          → G .F-hom f ⋆⟨ E ⟩ k c' h' .fst ≡ k c h .fst)

    module _ {d} {c c'} (h : CatIso D (F .F-ob c) d)(h' : CatIso D (F .F-ob c') d) where

      liftH : CatIso C c c'
      liftH = liftIso {F = F} (w-equiv .fullfaith) (⋆Iso h (invIso h'))

      liftH-eq' : F .F-hom (liftH .fst) ≡ h .fst ⋆⟨ D ⟩ h' .snd .inv
      liftH-eq' = cong fst (liftIso≡ {F = F} (w-equiv .fullfaith) (⋆Iso h (invIso h')))

      liftH-eq : F .F-hom (liftH .fst) ⋆⟨ D ⟩ h' .fst ≡ h .fst
      liftH-eq =
          cong (λ x → x ⋆⟨ D ⟩ _) liftH-eq'
        ∙ D .⋆Assoc _ _ _
        ∙ cong (λ x → _ ⋆⟨ D ⟩ x) (h' .snd .sec)
        ∙ D .⋆IdR _

    module _ (d : D .ob)(c₀ : C .ob)(h₀ : CatIso D (F .F-ob c₀) d) where

      isContrObj' : isContr (Obj d)
      isContrObj' .fst .fst = G .F-ob c₀
      isContrObj' .fst .snd .fst c h = F-Iso {F = G} (liftH h h₀)
      isContrObj' .fst .snd .snd c c' h h' f p = sym (G .F-seq _ _) ∙ cong (G .F-hom) g-path
        where
        g-path : f ⋆⟨ C ⟩ liftH h' h₀ .fst ≡ liftH h h₀ .fst
        g-path = isFullyFaithful→Faithful {F = F} (w-equiv .fullfaith) _ _ _ _
           (F .F-seq _ _
          ∙ cong (λ x → _ ⋆⟨ D ⟩ x) (liftH-eq' h' h₀)
          ∙ sym (D .⋆Assoc _ _ _)
          ∙ cong (λ x → x ⋆⟨ D ⟩ invIso h₀ .fst) p
          ∙ cong fst (sym (liftIso≡ {F = F} (w-equiv .fullfaith) (⋆Iso h (invIso h₀)))))
      isContrObj' .snd (e , k , coh) i .fst = CatIsoToPath (k c₀ h₀) i
      isContrObj' .snd (e , k , coh) i .snd .fst c h =
        let isom₀ = F-Iso {F = G} (liftH h h₀) in
        hcomp (λ j → λ
          { (i = i0) → isom₀
          ; (i = i1) → CatIso≡ (⋆Iso isom₀ (k c₀ h₀)) (k c h) (coh c c₀ h h₀ (liftH h h₀ .fst) (liftH-eq h h₀)) j })
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

    k : {d : D .ob}{c : C .ob}(h : CatIso D (F .F-ob c) d) → CatIso E (G .F-ob c) (Ext-ob d)
    k = isContrObj _ .fst .snd .fst _

    k-eq : {d : D .ob}{c c' : C .ob}
      (h : CatIso D (F .F-ob c) d)(h' : CatIso D (F .F-ob c') d)
      → (f : C [ c , c' ])
      → F .F-hom f ⋆⟨ D ⟩ h' .fst ≡ h .fst
      → G .F-hom f ⋆⟨ E ⟩ k h' .fst ≡ k h .fst
    k-eq = isContrObj _ .fst .snd .snd _ _

    Mor : (d d' : D .ob)(f : D [ d , d' ]) → Type _
    Mor d d' f =
      Σ[ g ∈ E [ Ext-ob d , Ext-ob d' ] ]
        ((c c' : C .ob)(h : CatIso D (F .F-ob c) d)(h' : CatIso D (F .F-ob c') d')
          → (l : C [ c , c' ])
          → F .F-hom l ⋆⟨ D ⟩ h' .fst ≡ h .fst ⋆⟨ D ⟩ f
          → G .F-hom l ⋆⟨ E ⟩ k h' .fst ≡ k h .fst ⋆⟨ E ⟩ g)

    module _ (d d' : D .ob)(f : D [ d , d' ])
      (c₀ : C .ob)(h₀ : CatIso D (F .F-ob c₀) d )
      (c₁ : C .ob)(h₁ : CatIso D (F .F-ob c₁) d')
      (l₀ : C [ c₀ , c₁ ])(p₀ : F .F-hom l₀ ⋆⟨ D ⟩ h₁ .fst ≡ h₀ .fst ⋆⟨ D ⟩ f)
      where

      g₀ = k h₀ .snd .inv ⋆⟨ E ⟩ G .F-hom l₀ ⋆⟨ E ⟩ k h₁ .fst

      isContrMor' : isContr (Mor d d' f)
      isContrMor' .fst .fst = g₀
      isContrMor' .fst .snd c c' h h' l p =
          cong (λ x → _ ⋆⟨ E ⟩ x) (⋆InvLMove (F-Iso {F = G} m') (k-eq h₁ h' _ m'-eq))
        ∙ sym (E .⋆Assoc _ _ _)
        ∙ cong (λ x → x ⋆⟨ E ⟩ k h₁ .fst) Gm-path'
        ∙ cong (λ x → x ⋆⟨ E ⟩ G .F-hom l₀ ⋆⟨ E ⟩ k h₁ .fst) m-eq'
        ∙ E .⋆Assoc _ _ _ ∙ E .⋆Assoc _ _ _
        ∙ cong (λ x → k h .fst ⋆⟨ E ⟩ x) (sym (E .⋆Assoc _ _ _))
        where
        m = liftH h₀ h
        m-eq = liftH-eq h₀ h
        m' = liftH h₁ h'
        m'-eq = liftH-eq h₁ h'

        m-eq' : G .F-hom (m .snd .inv) ≡ k h .fst ⋆⟨ E ⟩ k h₀ .snd .inv
        m-eq' = ⋆InvRMove (k h₀) (sym (⋆InvLMove (F-Iso {F = G} m) (k-eq h₀ h _ m-eq)))

        Fm-path : F .F-hom (l₀ ⋆⟨ C ⟩ m' .fst) ≡ F .F-hom (m .fst ⋆⟨ C ⟩ l)
        Fm-path =
            F .F-seq _ _
          ∙ cong (λ x → F .F-hom l₀ ⋆⟨ D ⟩ x) (liftH-eq' h₁ h')
          ∙ sym (D .⋆Assoc _ _ _)
          ∙ cong (λ x → x ⋆⟨ D ⟩ _) p₀
          ∙ cong (λ x → x ⋆⟨ D ⟩ _ ⋆⟨ D ⟩ _) (sym (D .⋆IdR _))
          ∙ cong (λ x → _ ⋆⟨ D ⟩ x ⋆⟨ D ⟩ _ ⋆⟨ D ⟩ _) (sym (h .snd .sec))
          ∙ cong (λ x → x ⋆⟨ D ⟩ _ ⋆⟨ D ⟩ _) (sym (D .⋆Assoc _ _ _))
          ∙ cong (λ x → x ⋆⟨ D ⟩ _) (D .⋆Assoc _ _ _)
          ∙ D .⋆Assoc _ _ _
          ∙ (λ i → ⋆InvRMove h m-eq (~ i) ⋆⟨ D ⟩ ⋆InvRMove h' p (~ i))
          ∙ sym (F .F-seq _ _)

        m-path : l₀ ⋆⟨ C ⟩ m' .fst ≡ m .fst ⋆⟨ C ⟩ l
        m-path = isFullyFaithful→Faithful {F = F} (w-equiv .fullfaith) _ _ _ _ Fm-path

        Gm-path : G .F-hom l₀ ⋆⟨ E ⟩ G .F-hom (m' .fst) ≡ G .F-hom (m .fst) ⋆⟨ E ⟩ G .F-hom l
        Gm-path = sym (G .F-seq _ _) ∙ cong (G .F-hom) m-path ∙ G .F-seq _ _

        Gm-path' : G .F-hom l ⋆⟨ E ⟩ G .F-hom (m' .snd .inv) ≡ G .F-hom (m .snd .inv) ⋆⟨ E ⟩ G .F-hom l₀
        Gm-path' = ⋆InvLMove (F-Iso {F = G} m) (sym (⋆InvRMove (F-Iso {F = G} m') Gm-path ∙ E .⋆Assoc _ _ _))

      isContrMor' .snd (g₁ , coh₁) i .fst =
         (⋆InvLMove (k h₀) (sym (isContrMor' .fst .snd c₀ c₁ h₀ h₁ l₀ p₀))
        ∙ sym (⋆InvLMove (k h₀) (sym (coh₁ c₀ c₁ h₀ h₁ l₀ p₀)))) i
      isContrMor' .snd x@(g₁ , coh₁) i .snd =
        isProp→PathP (λ i → isPropΠ6 (λ c c' h h' l _ →
          E .isSetHom
            (G .F-hom l ⋆⟨ E ⟩ k h' .fst)
            (k h .fst ⋆⟨ E ⟩ isContrMor' .snd x i .fst)))
        (isContrMor' .fst .snd) coh₁ i

    module _ {c c'} {d d'}
      (f : D [ d , d' ])(h : CatIso D (F .F-ob c) d)(h' : CatIso D (F .F-ob c') d')
      where

      liftL : C [ c , c' ]
      liftL = invEq (_ , w-equiv .fullfaith _ _) (h .fst ⋆⟨ D ⟩ f ⋆⟨ D ⟩ h' .snd .inv)

      liftL-eq : F .F-hom liftL ⋆⟨ D ⟩ h' .fst ≡ h .fst ⋆⟨ D ⟩ f
      liftL-eq =
        sym (⋆InvRMove (invIso h')
          (sym (secEq (_ , w-equiv .fullfaith _ _) (h .fst ⋆⟨ D ⟩ f ⋆⟨ D ⟩ h' .snd .inv))))

    isContrMor : (d d' : D .ob)(f : D [ d , d' ]) → isContr (Mor d d' f)
    isContrMor d d' f = Prop.rec2 isPropIsContr
      (λ (c₀ , h₀) (c₁ , h₁) →
        isContrMor' d d' f c₀ h₀ c₁ h₁ (liftL f h₀ h₁) (liftL-eq f h₀ h₁))
      (w-equiv .esssurj d) (w-equiv .esssurj d')

    Ext-hom : {d d' : D .ob}(f : D [ d , d' ]) → E [ Ext-ob d , Ext-ob d' ]
    Ext-hom f = isContrMor _ _ f .fst .fst

    liftL⋆ : ∀ {c c' c''} {d d' d''}
      (f : D [ d , d' ])(g : D [ d' , d'' ])
      (h : CatIso D (F .F-ob c) d)(h' : CatIso D (F .F-ob c') d')(h'' : CatIso D (F .F-ob c'') d'')
      → liftL (f ⋆⟨ D ⟩ g) h h'' ≡ liftL f h h' ⋆⟨ C ⟩ liftL g h' h''
    liftL⋆ f g h h' h'' = isFullyFaithful→Faithful {F = F} (w-equiv .fullfaith) _ _ _ _
      (⋆CancelR h'' path ∙ sym (F .F-seq _ _))
      where
      path : _
      path = liftL-eq (f ⋆⟨ D ⟩ g) h h''
        ∙ sym (D .⋆Assoc _ _ _)
        ∙ cong (λ x → x ⋆⟨ D ⟩ _) (sym (liftL-eq f h h'))
        ∙ D .⋆Assoc _ _ _
        ∙ cong (λ x → F .F-hom (liftL f h h') ⋆⟨ D ⟩ x) (sym (liftL-eq g h' h''))
        ∙ sym (D .⋆Assoc _ _ _)

    Ext : Functor D E
    Ext .F-ob  = Ext-ob
    Ext .F-hom = Ext-hom
    Ext .F-id {x = d} = Prop.rec (E .isSetHom _ _)
      (λ (c , h) →
        let r = isContrMor _ _ (D .id {x = d}) .fst .snd _ _ h h (C .id)
              (cong (λ x → x ⋆⟨ D ⟩ _) (F .F-id) ∙ D .⋆IdL _ ∙ sym (D .⋆IdR _))
        in  ⋆CancelL (k h) (sym r ∙ cong (λ x → x ⋆⟨ E ⟩ (k h .fst)) (G .F-id) ∙ E .⋆IdL _ ∙ sym (E .⋆IdR _)))
      (w-equiv .esssurj d)
    Ext .F-seq {x = a} {y = b} {z = c} f g =
      Prop.rec3 (E .isSetHom _ _)
      (λ (_ , ha) (_ , hb) (_ , hc) →
        let rf = isContrMor _ _ _ .fst .snd _ _ ha hb (liftL f ha hb) (liftL-eq f ha hb)
            rg = isContrMor _ _ _ .fst .snd _ _ hb hc (liftL g hb hc) (liftL-eq g hb hc)
            rfg = isContrMor _ _ _ .fst .snd _ _ ha hc (liftL (f ⋆⟨ D ⟩ g) ha hc) (liftL-eq (f ⋆⟨ D ⟩ g) ha hc)
        in  ⋆CancelL (k ha)
               (sym rfg
              ∙ cong (λ x → x ⋆⟨ E ⟩ k hc .fst) (cong (G .F-hom) (liftL⋆ f g ha hb hc) ∙ G .F-seq _ _)
              ∙ E .⋆Assoc _ _ _
              ∙ cong (λ x → G .F-hom _ ⋆⟨ E ⟩ x) rg
              ∙ sym (E .⋆Assoc _ _ _)
              ∙ cong (λ x → x ⋆⟨ E ⟩ Ext-hom g) rf
              ∙ E .⋆Assoc _ _ _))
      (w-equiv .esssurj a) (w-equiv .esssurj b) (w-equiv .esssurj c)

    objFc : (c : C .ob) → Obj (F .F-ob c)
    objFc c₀ .fst = G .F-ob c₀
    objFc c₀ .snd .fst c h = F-Iso {F = G} (liftIso {F = F} (w-equiv .fullfaith) h)
    objFc c₀ .snd .snd c c' h h' f p = sym (G .F-seq _ _)
      ∙ cong (G .F-hom) (isFullyFaithful→Faithful {F = F} (w-equiv .fullfaith) _ _ _ _ path)
      where
      path : _
      path =
          F .F-seq _ _
        ∙ cong (λ x → _ ⋆⟨ D ⟩ x) (cong fst (liftIso≡ {F = F} (w-equiv .fullfaith) h'))
        ∙ p ∙ sym (cong fst (liftIso≡ {F = F} (w-equiv .fullfaith) h))

    Ext-ob≡ : (c : C .ob) → Ext-ob (F .F-ob c) ≡ G .F-ob c
    Ext-ob≡ c₀ = cong fst (isContrObj _ .snd (objFc c₀))

    Ext-hom≡ : {c c' : C .ob}(f : C [ c , c' ])
      → PathP (λ i → E [ Ext-ob≡ c i , Ext-ob≡ c' i ]) (Ext-hom (F .F-hom f)) (G .F-hom f)
    Ext-hom≡  {c = c} {c' = c'} f i =
      hcomp (λ j → λ
        { (i = i0) → isContrMor _ _ _ .snd morFf (~ j) .fst
        ; (i = i1) → G .F-hom f })
      (transpGf-filler (~ i))
      where
      transpGf-filler = transport-filler (λ i → E [ Ext-ob≡ c (~ i) , Ext-ob≡ c' (~ i) ]) (G .F-hom f)

      morFf : Mor _ _ (F .F-hom f)
      morFf .fst = transpGf-filler i1
      morFf .snd c c' h h' l p =
        transport (λ i → G .F-hom l ⋆⟨ E ⟩ isContrObj _ .snd (objFc _) (~ i) .snd .fst c' h' .fst
          ≡ isContrObj _ .snd (objFc _) (~ i) .snd .fst c h .fst ⋆⟨ E ⟩ transpGf-filler i) G-path
        where
        F-path : _
        F-path =
            F .F-seq _ _
          ∙ cong (λ x → _ ⋆⟨ D ⟩ x) (cong fst (liftIso≡ {F = F} (w-equiv .fullfaith) h')) ∙ p
          ∙ cong (λ x → x ⋆⟨ D ⟩ _) (sym (cong fst (liftIso≡ {F = F} (w-equiv .fullfaith) h)))
          ∙ sym (F .F-seq _ _)

        G-path : _
        G-path =
            sym (G .F-seq _ _)
          ∙ cong (G .F-hom) (isFullyFaithful→Faithful {F = F} (w-equiv .fullfaith) _ _ _ _ F-path)
          ∙ G .F-seq _ _

    Ext≡ : precomposeF E F .F-ob Ext ≡ G
    Ext≡ = Functor≡ Ext-ob≡ Ext-hom≡

    Ext≃ : CatIso _ (precomposeF E F .F-ob Ext) G
    Ext≃ = NatIso→FUNCTORIso _ _ (pathToNatIso Ext≡)


  -- As a corollary, if F is weak equivalence and the target category is univalent, (- ∘ F) is a weak equivalence.

  isWeakEquiv→isWeakEquivPrecomp : isWeakEquivalence F → isWeakEquivalence (precomposeF E F)
  isWeakEquiv→isWeakEquivPrecomp w-equiv .fullfaith =
    isEssSurj+Full→isFullyFaithfulPrecomp E F (w-equiv .esssurj) (isFullyFaithful→Full {F = F} (w-equiv .fullfaith))
  isWeakEquiv→isWeakEquivPrecomp w-equiv .esssurj   = isWeakEquiv→isEssSurjPrecomp w-equiv

  -- Moreover, using assumption of being univalent, (- ∘ F) is actually an equivalence.

  isWeakEquiv→isEquivPrecomp : isWeakEquivalence F → isEquivalence (precomposeF E F)
  isWeakEquiv→isEquivPrecomp w-equiv =
    isWeakEquiv→isEquiv (isUnivalentFUNCTOR _ _ isUnivE) (isUnivalentFUNCTOR _ _ isUnivE)
      (isWeakEquiv→isWeakEquivPrecomp w-equiv)

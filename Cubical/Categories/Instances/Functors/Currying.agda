
module Cubical.Categories.Instances.Functors.Currying where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Instances.BinProduct
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Foundations.Function renaming (_∘_ to _∘→_)
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Equivalence.AdjointEquivalence
open import Cubical.Categories.Adjoint

private
  variable
    ℓC ℓC' ℓD ℓD' ℓE ℓE' : Level

module _ (C : Category ℓC ℓC') (D : Category ℓD ℓD') where
  open Category
  open NatTrans
  open Functor


  open Iso

  module _ (E : Category ℓE ℓE') where
    λF : Functor (E ×C C) D → Functor E (FUNCTOR C D)
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

    λFFunctor : Functor (FUNCTOR (E ×C C) D) (FUNCTOR E (FUNCTOR C D))
    F-ob λFFunctor = λF
    N-ob (F-hom λFFunctor x) _ =
     natTrans (curry (N-ob x) _) (curry (N-hom x) _)
    N-hom ((F-hom λFFunctor) x) _ =
     makeNatTransPath (funExt λ _ → N-hom x (_ , C .id))
    F-id λFFunctor = makeNatTransPath refl
    F-seq λFFunctor _ _ = makeNatTransPath refl

    λF⁻ : Functor E (FUNCTOR C D) → Functor (E ×C C) D
    F-ob (λF⁻ a) = uncurry (F-ob ∘→ F-ob a)
    F-hom (λF⁻ a) _ = N-ob (F-hom a _) _ ∘⟨ D ⟩ (F-hom (F-ob a _)) _
    F-id (λF⁻ a) = cong₂ (seq' D) (F-id (F-ob a _))
        (cong (flip N-ob _) (F-id a)) ∙ D .⋆IdL _
    F-seq (λF⁻ a) _ (eG , cG) =
     cong₂ (seq' D) (F-seq (F-ob a _) _ _) (cong (flip N-ob _)
           (F-seq a _ _))
          ∙ AssocCong₂⋆R D
              (N-hom ((F-hom a _) ●ᵛ (F-hom a _)) _ ∙
                (⋆Assoc D _ _ _) ∙
                  cong (seq' D _) (sym (N-hom (F-hom a eG) cG)))

    λF⁻Functor : Functor (FUNCTOR E (FUNCTOR C D)) (FUNCTOR (E ×C C) D)
    F-ob λF⁻Functor = λF⁻
    N-ob (F-hom λF⁻Functor x) = uncurry (N-ob ∘→ N-ob x)
    N-hom ((F-hom λF⁻Functor) {F} {F'} x) {xx} {yy} =
     uncurry λ hh gg →
                AssocCong₂⋆R D (cong N-ob (N-hom x hh) ≡$ _)
            ∙∙ cong (comp' D _) ((N-ob x (fst xx) .N-hom) gg)
            ∙∙ D .⋆Assoc _ _ _

    F-id λF⁻Functor = makeNatTransPath refl
    F-seq λF⁻Functor _ _ = makeNatTransPath refl

    isoλF : Iso (Functor (E ×C C) D) (Functor E (FUNCTOR C D))
    fun isoλF = λF
    inv isoλF = λF⁻
    sec isoλF b = Functor≡ (λ _ → Functor≡ (λ _ → refl)
      λ _ → cong (seq' D _) (congS (flip N-ob _) (F-id b)) ∙ D .⋆IdR _)
      λ _ → makeNatTransPathP _ _
        (funExt λ _ → cong (comp' D _) (F-id (F-ob b _)) ∙ D .⋆IdL _)
    ret isoλF a = Functor≡ (λ _ → refl) λ _ → sym (F-seq a _ _)
          ∙ cong (F-hom a) (cong₂ _,_ (E .⋆IdL _) (C .⋆IdR _))

    open AdjointEquivalence


    𝟙≅ᶜλF⁻∘λF : 𝟙⟨ FUNCTOR (E ×C C) D ⟩ ≅ᶜ λF⁻Functor ∘F λFFunctor
    𝟙≅ᶜλF⁻∘λF = pathToNatIso $
         Functor≡ (λ x → Functor≡ (λ _ → refl)
                  λ _ → cong (F-hom x) (cong₂ _,_ (sym (E .⋆IdL _)) (sym (C .⋆IdR _)))
                    ∙ F-seq x _ _)
              λ _ → makeNatTransPathP _ _ refl

    λF∘λF⁻≅ᶜ𝟙 : λFFunctor ∘F λF⁻Functor ≅ᶜ 𝟙⟨ FUNCTOR E (FUNCTOR C D) ⟩
    λF∘λF⁻≅ᶜ𝟙 = pathToNatIso $ Functor≡
      (λ x → Functor≡
         (λ _ → Functor≡ (λ _ → refl) λ _ → cong (D ⋆ F-hom (F-ob x _) _)
                   (cong N-ob (F-id x) ≡$ _) ∙ D .⋆IdR _)
         λ _ → makeNatTransPathP _ _
                    (funExt λ _ → cong (comp' D _) (F-id (F-ob x _)) ∙ D .⋆IdL _))
         λ _ → makeNatTransPathP _ _ (funExt λ _ → makeNatTransPathP _ _ refl)

    open UnitCounit.TriangleIdentities

    FunctorCurryAdjointEquivalence :
      AdjointEquivalence (FUNCTOR (E ×C C) D) (FUNCTOR E (FUNCTOR C D))
    fun FunctorCurryAdjointEquivalence = λFFunctor
    inv FunctorCurryAdjointEquivalence = λF⁻Functor
    η FunctorCurryAdjointEquivalence = 𝟙≅ᶜλF⁻∘λF
    ε FunctorCurryAdjointEquivalence = λF∘λF⁻≅ᶜ𝟙
    Δ₁ (triangleIdentities FunctorCurryAdjointEquivalence) c = makeNatTransPath $
      funExt λ _ → makeNatTransPath (funExt λ _ → cong (∘diag $ seq' D)
        (congP₂$ (transport-fillerExt⁻ (cong (D End[_] ∘→ c ⟅_⟆) (transportRefl _))) λ _ → D .id)
      ∙ D .⋆IdR _)

    Δ₂ (triangleIdentities FunctorCurryAdjointEquivalence) d = makeNatTransPath $
      funExt λ _ → cong (∘diag $ seq' D)
        (congP₂$ (transport-fillerExt⁻ (cong (D End[_] ∘→  uncurry (F-ob ∘→ F-ob d))
              (transportRefl _))) λ _ → D .id)
      ∙ D .⋆IdR _


{-# OPTIONS --safe #-}

module Cubical.Categories.Instances.Functors.Currying where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Equiv

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Constructions.BinProduct.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Foundations.Function renaming (_∘_ to _∘→_)
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Equivalence.AdjointEquivalence
open import Cubical.Categories.Adjoint
open import Cubical.Categories.Equivalence
open import Cubical.Categories.Equivalence.Base

open import Cubical.Tactics.CategorySolver.Reflection
open import Cubical.HITs.PropositionalTruncation

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
          ∙ AssocCong₂⋆R {C = D} _
              (N-hom ((F-hom a _) ●ᵛ (F-hom a _)) _ ∙
                (⋆Assoc D _ _ _) ∙
                  cong (seq' D _) (sym (N-hom (F-hom a eG) cG)))

    λF⁻Functor : Functor (FUNCTOR E (FUNCTOR C D)) (FUNCTOR (E ×C C) D)
    F-ob λF⁻Functor = λF⁻
    N-ob (F-hom λF⁻Functor x) = uncurry (N-ob ∘→ N-ob x)
    N-hom ((F-hom λF⁻Functor) {F} {F'} x) {xx} {yy} =
     uncurry λ hh gg →
                AssocCong₂⋆R {C = D} _ (cong N-ob (N-hom x hh) ≡$ _)
            ∙∙ cong (comp' D _) ((N-ob x (fst xx) .N-hom) gg)
            ∙∙ D .⋆Assoc _ _ _

    F-id λF⁻Functor = makeNatTransPath refl
    F-seq λF⁻Functor _ _ = makeNatTransPath refl

    isoλF : Iso (Functor (E ×C C) D) (Functor E (FUNCTOR C D))
    fun isoλF = λF
    inv isoλF = λF⁻
    rightInv isoλF b = Functor≡ (λ _ → Functor≡ (λ _ → refl)
      λ _ → cong (seq' D _) (congS (flip N-ob _) (F-id b)) ∙ D .⋆IdR _)
      λ _ → makeNatTransPathP _ _
        (funExt λ _ → cong (comp' D _) (F-id (F-ob b _)) ∙ D .⋆IdL _)
    leftInv isoλF a = Functor≡ (λ _ → refl) λ _ → sym (F-seq a _ _)
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

    -- The action of currying out the right argument of a Functor (E ×C C) D
    λFr : Functor (E ×C C) D → Functor E (FUNCTOR C D)
    λFr F .F-ob a .F-ob b = F ⟅ a , b ⟆
    λFr F .F-ob a .F-hom f = F .F-hom (E .id , f)
    λFr F .F-ob a .F-id = F .F-id
    λFr F .F-ob a .F-seq f g =
      F .F-hom (E .id , f ⋆⟨ C ⟩ g)
        ≡⟨ (λ i → F .F-hom ((E .⋆IdL (E .id) (~ i)) , f ⋆⟨ C ⟩ g)) ⟩
      F .F-hom (E .id ⋆⟨ E ⟩ E .id , f ⋆⟨ C ⟩ g)
        ≡⟨ F .F-seq (E .id , f) (E .id , g) ⟩
      F .F-hom (E .id , f) ⋆⟨ D ⟩ F .F-hom (E .id , g ) ∎
    λFr F .F-hom γ .N-ob b = F .F-hom (γ , C .id)
    λFr F .F-hom γ .N-hom f =
      F .F-hom (E .id , f) ⋆⟨ D ⟩ F .F-hom (γ , C .id)
        ≡⟨ sym (F .F-seq (E .id , f) (γ , C .id)) ⟩
      F .F-hom (E .id ⋆⟨ E ⟩ γ , f ⋆⟨ C ⟩ C .id)
        ≡⟨ (λ i → F .F-hom ((idTrans (Id {C = E}) .N-hom γ (~ i)) ,
                             idTrans (Id {C = C}) .N-hom f i)) ⟩
      F .F-hom (γ ⋆⟨ E ⟩ E .id , C .id ⋆⟨ C ⟩ f)
        ≡⟨ F .F-seq (γ , C .id) (E .id , f) ⟩
      F .F-hom (γ , C .id) ⋆⟨ D ⟩ F .F-hom (E .id , f)  ∎
    λFr F .F-id = makeNatTransPath (funExt (λ a → F .F-id))
    λFr F .F-seq γ δ = makeNatTransPath (funExt (λ a →
        F .F-hom (γ ⋆⟨ E ⟩ δ , C .id)
          ≡⟨ (λ i → F .F-hom (γ ⋆⟨ E ⟩ δ , C .⋆IdL (C .id) (~ i))) ⟩
        F .F-hom (γ ⋆⟨ E ⟩ δ , C .id ⋆⟨ C ⟩ C .id)
          ≡⟨ F .F-seq (γ , C .id) (δ , C .id) ⟩
        F .F-hom (γ , C .id) ⋆⟨ D ⟩ F .F-hom (δ , C .id) ∎))

    -- Functorially extend the currying action from a
    -- function on objects to a functor between
    -- the relevant functor categories
    -- Here "currying" pulls out the right argument.
    -- We will define a similar left-sided version
    -- under the name curryFl
    curryF : Functor (FUNCTOR (E ×C C) D) (FUNCTOR E (FUNCTOR C D))
    curryF .F-ob = λFr
    curryF .F-hom η .N-ob γ .N-ob c = η .N-ob (γ , c)
    curryF .F-hom η .N-ob γ .N-hom ϕ = η .N-hom (E .id , ϕ)
    curryF .F-hom η .N-hom f =
      makeNatTransPath (funExt (λ (c : C .ob) → η .N-hom (f , C .id)))
    curryF .F-id = makeNatTransPath (funExt λ (γ : E .ob) → refl)
    curryF .F-seq η η' = makeNatTransPath (funExt λ (γ : E .ob) → refl)

    -- Preimage for the ESO proof
    -- i.e. an object in (FUNCTOR E (FUNCTOR C D)) that maps to λF
    curryF-ESO-object-preimage : (FUNCTOR E (FUNCTOR C D)) .ob →
                                 (FUNCTOR (E ×C C) D) .ob
    curryF-ESO-object-preimage λF .F-ob (γ , c) =  λF .F-ob γ .F-ob c
    curryF-ESO-object-preimage λF .F-hom
      {x = (γ₁ , c₁)} {y = (γ₂ , c₂)} (ϕ , ψ) =
        λF .F-hom ϕ .N-ob c₁ ⋆⟨ D ⟩ λF .F-ob γ₂ .F-hom ψ
    curryF-ESO-object-preimage λF .F-seq
      {x = (γ₁ , c₁)} {y = (γ₂ , c₂)} {z = (γ₃ , c₃)} (ϕ₁ , ψ₁) (ϕ₂ , ψ₂) = (
      curryF-ESO-object-preimage λF .F-hom ((ϕ₁ , ψ₁) ⋆⟨ E ×C C ⟩ (ϕ₂ , ψ₂))
        ≡⟨ ((λ i → ( (λF .F-seq ϕ₁ ϕ₂ (i) ) .N-ob c₁ ⋆⟨ D ⟩
          λF .F-ob γ₃ .F-hom (ψ₁ ⋆⟨ C ⟩ ψ₂)))) ⟩
      (λF .F-hom ϕ₁ ⋆⟨ FUNCTOR C D ⟩ λF .F-hom ϕ₂) .N-ob c₁ ⋆⟨ D ⟩
        λF .F-ob γ₃ .F-hom (ψ₁ ⋆⟨ C ⟩ ψ₂)
        ≡⟨ (λ i → (λF .F-hom ϕ₁ .N-ob c₁ ⋆⟨ D ⟩
           λF .F-hom ϕ₂ .N-ob c₁ ⋆⟨ D ⟩ λF .F-ob γ₃ .F-seq ψ₁ ψ₂ i)) ⟩
      (λF .F-hom ϕ₁ .N-ob c₁ ⋆⟨ D ⟩
        λF .F-hom ϕ₂ .N-ob c₁) ⋆⟨ D ⟩
          (λF .F-ob γ₃ .F-hom ψ₁ ⋆⟨ D ⟩ λF .F-ob γ₃ .F-hom ψ₂)
        ≡⟨ solveCat! D ⟩
      λF .F-hom ϕ₁ .N-ob c₁ ⋆⟨ D ⟩ (λF .F-hom ϕ₂ .N-ob c₁ ⋆⟨ D ⟩
        λF .F-ob γ₃ .F-hom ψ₁) ⋆⟨ D ⟩ λF .F-ob γ₃ .F-hom ψ₂
        ≡⟨ ((λ i → ( λF .F-hom ϕ₁ .N-ob c₁ ⋆⟨ D ⟩
          (λF .F-hom ϕ₂ .N-hom ψ₁ (~ i) ) ⋆⟨ D ⟩ λF .F-ob γ₃ .F-hom ψ₂ ))) ⟩
      λF .F-hom ϕ₁ .N-ob c₁ ⋆⟨ D ⟩ (λF .F-ob γ₂ .F-hom ψ₁ ⋆⟨ D ⟩
        λF .F-hom ϕ₂ .N-ob c₂) ⋆⟨ D ⟩ λF .F-ob γ₃ .F-hom ψ₂
        ≡⟨ solveCat! D ⟩
      curryF-ESO-object-preimage λF .F-hom (ϕ₁ , ψ₁) ⋆⟨ D ⟩
        curryF-ESO-object-preimage λF .F-hom (ϕ₂ , ψ₂) ∎)
    curryF-ESO-object-preimage λF .F-id  {x = (γ , c)} = (
      curryF-ESO-object-preimage λF .F-hom (E .id , C .id)
        ≡⟨ ((λ i → (λF .F-id i .N-ob c ⋆⟨ D ⟩ λF .F-ob γ .F-hom (C .id)))) ⟩
      D .id ⋆⟨ D ⟩ λF .F-ob γ .F-hom (C .id)
        ≡⟨ ((λ i → (D .id ⋆⟨ D ⟩ (λF .F-ob γ .F-id i)))) ⟩
      D .id ⋆⟨ D ⟩ D .id
        ≡⟨ D .⋆IdL (D .id) ⟩
      D .id
      ∎ )
    -- Half of the isomorphism between (curryF-ESO-object-preimage λF) and λF
    curryF-ESO-morphism-preimage : (λF : (FUNCTOR E (FUNCTOR C D)) .ob) →
                                   NatTrans
                                     (curryF .F-ob
                                       (curryF-ESO-object-preimage λF))
                                     λF
    curryF-ESO-morphism-preimage λF .N-ob γ .N-ob c = D .id
    curryF-ESO-morphism-preimage λF .N-ob γ .N-hom {x = c₁} {y = c₂} ψ =
      ((λF .F-hom (E .id) .N-ob c₁) ⋆⟨ D ⟩ (λF .F-ob γ .F-hom ψ)) ⋆⟨ D ⟩ D .id
        ≡⟨ (λ i → (D .⋆IdR ((λF .F-hom (E .id) .N-ob c₁) ⋆⟨ D ⟩
          (λF .F-ob γ .F-hom ψ)) (i) )) ⟩
      (λF .F-hom (E .id) .N-ob c₁) ⋆⟨ D ⟩ λF .F-ob γ .F-hom ψ
        ≡⟨ ((λ i → ((λF .F-id i) .N-ob c₁ ⋆⟨ D ⟩ λF .F-ob γ .F-hom ψ ))) ⟩
      D .id ⋆⟨ D ⟩ λF .F-ob γ .F-hom ψ ∎
    curryF-ESO-morphism-preimage λF .N-hom {x = γ₁} {y = γ₂} ϕ =
      makeNatTransPath (funExt (λ (c : C .ob) →
      curryF .F-ob (curryF-ESO-object-preimage λF) .F-hom ϕ .N-ob c ⋆⟨ D ⟩
        (curryF-ESO-morphism-preimage λF) .N-ob γ₂ .N-ob c
        ≡⟨ D .⋆IdR
          (curryF .F-ob (curryF-ESO-object-preimage λF) .F-hom ϕ .N-ob c) ⟩
      λF .F-hom ϕ .N-ob c ⋆⟨ D ⟩ λF .F-ob γ₂ .F-hom (C .id)
        ≡⟨ ((λ i → (λF .F-hom ϕ .N-ob c ⋆⟨ D ⟩ λF .F-ob γ₂ .F-id i))) ⟩
      λF .F-hom ϕ .N-ob c ⋆⟨ D ⟩ D .id
        ≡⟨ D .⋆IdR (λF .F-hom ϕ .N-ob c) ⟩
      λF .F-hom ϕ .N-ob c
        ≡⟨ ((λ i → (D .⋆IdL (λF .F-hom ϕ .N-ob c) (~ i) ))) ⟩
      (curryF-ESO-morphism-preimage λF) .N-ob γ₁ .N-ob c ⋆⟨ D ⟩
        λF .F-hom ϕ .N-ob c ∎))

    open isIsoC

    -- Show that curryF-ESO-morphism-preimage is indeed an isomorphism in
    -- FUNCTOR E (FUNCTOR C D)
    curryF-ESO-morphism-preimage-isIso : (λF : (FUNCTOR E (FUNCTOR C D)) .ob) →
                                         isIsoC
                                           (FUNCTOR E (FUNCTOR C D))
                                           (curryF-ESO-morphism-preimage λF)
    curryF-ESO-morphism-preimage-isIso λF .inv .N-ob γ .N-ob c =  D .id
    curryF-ESO-morphism-preimage-isIso λF .inv .N-ob γ .N-hom
      {x = c₁} {y = c₂} ψ =
      λF .F-ob γ .F-hom ψ ⋆⟨ D ⟩ D .id
        ≡⟨ D .⋆IdR (λF .F-ob γ .F-hom ψ) ⟩
      λF .F-ob γ .F-hom ψ
        ≡⟨ (λ i → (D .⋆IdL (λF .F-ob γ .F-hom ψ) (~ i))) ⟩
      D .id ⋆⟨ D ⟩ λF .F-ob γ .F-hom ψ
        ≡⟨ ((λ i → (λF .F-id (~ i)) .N-ob c₁ ⋆⟨ D ⟩ λF .F-ob γ .F-hom ψ ) ) ⟩
     curryF .F-ob (curryF-ESO-object-preimage λF) .F-ob γ .F-hom ψ
        ≡⟨ ((λ i → (D .⋆IdL
          (curryF .F-ob (curryF-ESO-object-preimage λF) .F-ob γ .F-hom ψ )
            (~ i) ))) ⟩
      D .id ⋆⟨ D ⟩
        curryF .F-ob (curryF-ESO-object-preimage λF) .F-ob γ .F-hom ψ ∎
    curryF-ESO-morphism-preimage-isIso λF .inv .N-hom {x = γ₁} {y = γ₂} ϕ =
      makeNatTransPath (funExt (λ (c : C .ob ) →
      λF .F-hom ϕ .N-ob c ⋆⟨ D ⟩
        curryF-ESO-morphism-preimage-isIso λF .inv .N-ob γ₂ .N-ob c
        ≡⟨ D .⋆IdR (λF .F-hom ϕ .N-ob c) ⟩
      λF .F-hom ϕ .N-ob c
        ≡⟨ ((λ i → (D .⋆IdR (λF .F-hom ϕ .N-ob c) (~ i)))) ⟩
      λF .F-hom ϕ .N-ob c ⋆⟨ D ⟩ D .id
        ≡⟨ ((λ i → ( λF .F-hom ϕ .N-ob c ⋆⟨ D ⟩ λF .F-ob γ₂ .F-id (~ i )))) ⟩
      λFr (curryF-ESO-object-preimage λF) .F-hom ϕ .N-ob c
        ≡⟨ ((λ i → ((D .⋆IdL (λFr (curryF-ESO-object-preimage λF)
          .F-hom ϕ .N-ob c) (~ i)) ))) ⟩
      D .id ⋆⟨ D ⟩ λFr (curryF-ESO-object-preimage λF) .F-hom ϕ .N-ob c ∎
      ))
    curryF-ESO-morphism-preimage-isIso λF .sec =
      makeNatTransPath (funExt (λ (γ : E .ob) →
      makeNatTransPath (funExt (λ (c : C .ob) →
        curryF-ESO-morphism-preimage-isIso λF .inv .N-ob γ .N-ob c ⋆⟨ D ⟩
          curryF-ESO-morphism-preimage λF .N-ob γ .N-ob c
          ≡⟨ D .⋆IdR
            (curryF-ESO-morphism-preimage-isIso λF .inv .N-ob γ .N-ob c) ⟩
        D .id ∎
      ))))
    curryF-ESO-morphism-preimage-isIso λF .ret =
      makeNatTransPath (funExt (λ (γ : E .ob) →
      makeNatTransPath (funExt (λ (c : C .ob) →
         curryF-ESO-morphism-preimage λF .N-ob γ .N-ob c ⋆⟨ D ⟩
           curryF-ESO-morphism-preimage-isIso λF .inv .N-ob γ .N-ob c
          ≡⟨ D .⋆IdR
            (curryF-ESO-morphism-preimage-isIso λF .inv .N-ob γ .N-ob c) ⟩
        D .id ∎
      ))))


    -- to prove that curryF is an equivalence,
    -- we construct the inverse functor, uncurryF
    uncurryF : Functor (FUNCTOR E (FUNCTOR C D)) (FUNCTOR (E ×C C) D)
    uncurryF .F-ob λF = curryF-ESO-object-preimage λF
    -- stolen from curryF-full-preimage
    uncurryF .F-hom {F} {G} λη .N-ob (γ , c) = λη .N-ob γ .N-ob c
    uncurryF .F-hom {F} {G} λη .N-hom {(γ₁ , c₁)} {(γ₂ , c₂)} (ϕ₁ , ϕ₂) =
      uncurryF .F-ob F .F-hom (ϕ₁ , ϕ₂) ⋆⟨ D ⟩
        uncurryF .F-hom λη .N-ob (γ₂ , c₂)
        ≡⟨ solveCat! D ⟩
      F .F-hom (ϕ₁) .N-ob c₁ ⋆⟨ D ⟩ (F .F-ob γ₂ .F-hom ϕ₂ ⋆⟨ D ⟩
        λη .N-ob γ₂ .N-ob c₂)
        ≡⟨ (λ i → (F .F-hom (ϕ₁) .N-ob c₁ ⋆⟨ D ⟩ (λη .N-ob γ₂ .N-hom ϕ₂ (i)))) ⟩
      F .F-hom (ϕ₁) .N-ob c₁ ⋆⟨ D ⟩
        (λη .N-ob γ₂ .N-ob c₁ ⋆⟨ D ⟩ G .F-ob γ₂ .F-hom ϕ₂)
        ≡⟨ solveCat! D ⟩
      (F .F-hom (ϕ₁) .N-ob c₁ ⋆⟨ D ⟩
        λη .N-ob γ₂ .N-ob c₁) ⋆⟨ D ⟩ G .F-ob γ₂ .F-hom ϕ₂
       ≡⟨ (λ i → (((λη .N-hom (ϕ₁) (i)) .N-ob c₁) ⋆⟨ D ⟩
         G .F-ob γ₂ .F-hom ϕ₂)) ⟩
      (λη .N-ob γ₁ .N-ob c₁ ⋆⟨ D ⟩ G .F-hom (ϕ₁) .N-ob c₁) ⋆⟨ D ⟩
        G .F-ob γ₂ .F-hom ϕ₂
        ≡⟨ solveCat! D ⟩
      uncurryF .F-hom λη .N-ob (γ₁ , c₁) ⋆⟨ D ⟩
        uncurryF .F-ob G .F-hom (ϕ₁ , ϕ₂) ∎
    uncurryF .F-id = makeNatTransPath (funExt (λ x → refl ))
    uncurryF .F-seq λη₁ λη₂ = makeNatTransPath (funExt (λ x → refl ))


    open WeakInverse
    open NatIso

    -- curryF is an equivalence. Done using η ε isos constructed explicitly.
    -- most of the time, these are the identity
    curryF-isEquivalence : WeakInverse curryF
    curryF-isEquivalence =
      record { invFunc = uncurryF ; η = η-iso ; ε = ε-iso } where
      -- separate definition to sidestep Agda termination issue
      η-trans : NatTrans 𝟙⟨ FUNCTOR (E ×C C) D ⟩ (uncurryF ∘F curryF)
      η-trans .N-ob F .N-ob (γ , c) = D .id
      η-trans .N-ob F .N-hom {(γ₁ , c₁)} {(γ₂ , c₂)} (ϕ₁ , ϕ₂) =
        (F .F-hom (ϕ₁ , ϕ₂)) ⋆⟨ D ⟩ D .id
          ≡⟨ (λ i →
            (F .F-hom ((E .⋆IdR ϕ₁) (~ i) , (C .⋆IdL ϕ₂) (~ i)) ⋆⟨ D ⟩ D .id)) ⟩
        (F .F-hom ((ϕ₁ , C .id) ⋆⟨ E ×C C ⟩ (E .id , ϕ₂))) ⋆⟨ D ⟩ D .id
          ≡⟨ (λ i → (F .F-seq (ϕ₁ , C .id) (E .id , ϕ₂)) (i) ⋆⟨ D ⟩ D .id) ⟩
        (F .F-hom (ϕ₁ , C .id) ⋆⟨ D ⟩ F .F-hom (E .id , ϕ₂)) ⋆⟨ D ⟩ D .id
          ≡⟨ solveCat! D ⟩
        D .id ⋆⟨ D ⟩ ((uncurryF ∘F curryF) .F-ob F) .F-hom (ϕ₁ , ϕ₂)  ∎
      η-trans .N-hom {F} {G} β =
        makeNatTransPath (funExt (λ (γ , c) → solveCat! D))

      η-iso : NatIso 𝟙⟨ FUNCTOR (E ×C C) D ⟩ (uncurryF ∘F curryF)
      η-iso .trans = η-trans

      η-iso .nIso F .inv .N-ob (γ , c) = D .id
      η-iso .nIso F .inv .N-hom {(γ₁ , c₁)} {(γ₂ , c₂)} (ϕ₁ , ϕ₂) =
        ((uncurryF ∘F curryF) .F-ob F) .F-hom (ϕ₁ , ϕ₂) ⋆⟨ D ⟩ D .id
          ≡⟨ solveCat! D ⟩
        D .id ⋆⟨ D ⟩ ((uncurryF ∘F curryF) .F-ob F) .F-hom (ϕ₁ , ϕ₂)
          ≡⟨ sym (η-iso .trans .N-ob F .N-hom (ϕ₁ , ϕ₂)) ⟩
        (F .F-hom (ϕ₁ , ϕ₂)) ⋆⟨ D ⟩ D .id
          ≡⟨ solveCat! D ⟩
        D .id ⋆⟨ D ⟩ (F .F-hom (ϕ₁ , ϕ₂))  ∎
      η-iso .nIso F .sec = makeNatTransPath (funExt (λ (γ , c) → solveCat! D))
      η-iso .nIso F .ret = makeNatTransPath (funExt (λ (γ , c) → solveCat! D))

      ε-iso : NatIso (curryF ∘F uncurryF) 𝟙⟨ FUNCTOR E (FUNCTOR C D) ⟩
      ε-iso .trans .N-ob λF = curryF-ESO-morphism-preimage λF
      ε-iso .trans .N-hom {λF} {λG} λβ = makeNatTransPath (funExt (λ γ →
        makeNatTransPath (funExt (λ c →
          -- TODO: For some reason this doesn't simplify to just solvecat...
          (λβ .N-ob γ .N-ob c) ⋆⟨ D ⟩ D .id
            ≡⟨ solveCat! D ⟩
          D .id ⋆⟨ D ⟩ λβ .N-ob γ .N-ob c ∎ ))))
      ε-iso .nIso = (λ λF → curryF-ESO-morphism-preimage-isIso λF)


    open Cubical.Categories.Equivalence.Base._≃ᶜ_

    curryEquivalence : FUNCTOR (E ×C C) D ≃ᶜ FUNCTOR E (FUNCTOR C D)
    curryEquivalence .func = curryF
    curryEquivalence ._≃ᶜ_.isEquiv = ∣ curryF-isEquivalence ∣₁

    -- We also want a notion of currying out the left argument.
    -- We do this by composing
    -- a swapping functor with the right-sided currying functor
    -- To show that this left-handed currying is also an equivalence,
    -- we will need to show that
    -- the swapping functor is an equivalence
    swapArgs : Functor (FUNCTOR (C ×C E) D) (FUNCTOR (E ×C C) D)
    swapArgs .F-ob F .F-ob (c , γ) = F .F-ob (γ , c)
    swapArgs .F-ob F .F-hom (ψ , ϕ) = F .F-hom (ϕ , ψ)
    swapArgs .F-ob F .F-id = F .F-id
    swapArgs .F-ob F .F-seq (ψ₁ , ϕ₁) (ψ₂ , ϕ₂) = F .F-seq (ϕ₁ , ψ₁) (ϕ₂ , ψ₂)
    swapArgs .F-hom η .N-ob (γ , c) = η .N-ob (c , γ)
    swapArgs .F-hom η .N-hom (ϕ , ψ) = η .N-hom (ψ , ϕ)
    swapArgs .F-id = makeNatTransPath (funExt λ (γ , c) → refl)
    swapArgs .F-seq η η' = makeNatTransPath (funExt λ (γ , c) → refl)

    swapArgs-inv : Functor (FUNCTOR (E ×C C) D) (FUNCTOR (C ×C E) D)
    swapArgs-inv .F-ob F .F-ob (γ , c) = F .F-ob (c , γ)
    swapArgs-inv .F-ob F .F-hom (ϕ , ψ) = F .F-hom (ψ , ϕ)
    swapArgs-inv .F-ob F .F-id = F .F-id
    swapArgs-inv .F-ob F .F-seq (ϕ₁ , ψ₁) (ϕ₂ , ψ₂) =
      F .F-seq (ψ₁ , ϕ₁) (ψ₂ , ϕ₂)
    swapArgs-inv .F-hom η .N-ob (γ , c) = η .N-ob (c , γ)
    swapArgs-inv .F-hom η .N-hom (ψ , ϕ) = η .N-hom (ϕ , ψ)
    swapArgs-inv .F-id = makeNatTransPath (funExt λ (γ , c) → refl)
    swapArgs-inv .F-seq η η' = makeNatTransPath (funExt λ (γ , c) → refl)

    swapArgs-isEquivalence : WeakInverse swapArgs
    swapArgs-isEquivalence =
      record { invFunc = swapArgs-inv ; η = the-η ; ε = the-ε } where
      η-morphisms : N-ob-Type 𝟙⟨ FUNCTOR (C ×C E) D ⟩
                              (funcComp swapArgs-inv swapArgs)
      η-morphisms F .N-ob γ = D .id
      η-morphisms F .N-hom ϕ = solveCat! D

      the-η : NatIso 𝟙⟨ FUNCTOR (C ×C E) D ⟩ (funcComp swapArgs-inv swapArgs)
      the-η .trans .N-ob = η-morphisms
      the-η .trans .N-hom α =
        makeNatTransPath (funExt (λ (c , γ) → solveCat! D))
      the-η .nIso F .inv .N-ob (c , γ) = D .id
      the-η .nIso F .inv .N-hom (ψ , ϕ) = solveCat! D
      the-η .nIso F .sec = makeNatTransPath (funExt (λ (c , γ) → solveCat! D))
      the-η .nIso F .ret = makeNatTransPath (funExt (λ (c , γ) → solveCat! D))

      ε-morphisms : N-ob-Type (funcComp swapArgs swapArgs-inv)
                              𝟙⟨ FUNCTOR (E ×C C) D ⟩
      ε-morphisms F .N-ob c = D .id
      ε-morphisms F .N-hom ψ = solveCat! D

      the-ε : NatIso (funcComp swapArgs swapArgs-inv) 𝟙⟨ FUNCTOR (E ×C C) D ⟩
      the-ε .trans .N-ob = ε-morphisms
      the-ε .trans .N-hom α =
        makeNatTransPath (funExt (λ (γ , c) → solveCat! D))
      the-ε .nIso F .inv .N-ob (γ , c) = D .id
      the-ε .nIso F .inv .N-hom (φ , ψ) = solveCat! D
      the-ε .nIso F .sec = makeNatTransPath (funExt (λ (γ , c) → solveCat! D))
      the-ε .nIso F .ret = makeNatTransPath (funExt (λ (γ , c) → solveCat! D))

    curryFl : Functor (FUNCTOR (C ×C E) D) (FUNCTOR E (FUNCTOR C D))
    curryFl = curryF ∘F swapArgs


    curryFl-isEquivalence : WeakInverse curryFl
    curryFl-isEquivalence =
      isEquivalenceComp swapArgs-isEquivalence curryF-isEquivalence

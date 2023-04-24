{-# OPTIONS --safe #-}

module Cubical.Categories.TypesOfCategories.TypeCategory where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
import Cubical.Functions.Fibration as Fibration

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Limits.Pullback
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Sets


open Fibration.ForSets

record isTypeCategory {ℓ ℓ' ℓ''} (C : Category ℓ ℓ')
       : Type (ℓ-max ℓ (ℓ-max ℓ' (ℓ-suc ℓ''))) where
  open Category C
  open Cospan

  field
    -- a Type of types over a context
    Ty[_] : ob → Type ℓ''
    -- extend a context with a type
    cext : ∀ (Γ : _) → (A : Ty[ Γ ]) → Σ[ ΓA ∈ ob ] (C [ ΓA , Γ ])

  -- the new object from a context extension
  _⍮_ : (Γ : _) → (A : Ty[ Γ ]) → ob
  Γ ⍮ A = fst (cext Γ A)

  -- the projection from the extended context to the original
  π : (Γ : _) → (A : Ty[ Γ ]) → C [ Γ ⍮ A , Γ ]
  π Γ A = snd (cext Γ A)

  field
    -- pullback over context extentions
    reindex : ∀ {Γ' Γ}
            → C [ Γ' , Γ ]
            → (Ty[ Γ ] → Ty[ Γ' ])

    q⟨_,_⟩ : ∀ {Γ' Γ}
           → (f : C [ Γ' , Γ ])
           → (A : Ty[ Γ ])
           → C [ Γ' ⍮ (reindex f A) , Γ ⍮ A ]

    sq : ∀ {Γ' Γ : ob} (f : C [ Γ' , Γ ]) (A : Ty[ Γ ])
       → π Γ' (reindex f A) ⋆ f ≡ q⟨ f , A ⟩ ⋆ π Γ A

    isPB : ∀ {Γ' Γ : ob} (f : C [ Γ' , Γ ]) (A : Ty[ Γ ])
         → isPullback C (cospan Γ' Γ (Γ ⍮ A) f (π Γ A))
                      (π Γ' (reindex f A)) (q⟨ f , A ⟩) (sq f A)

-- presheaves are type contexts
module _ {ℓ ℓ' ℓ'' : Level} (C : Category ℓ ℓ') where
  open isTypeCategory
  open Category
  open Functor
  open NatTrans

  private
    isSurjSET : ∀ {ℓ} {A B : SET ℓ .ob} → (f : SET ℓ [ A , B ]) → Type _
    isSurjSET {A = A} {B} f = ∀ (b : fst B) → Σ[ a ∈ fst A ] f a ≡ b

    -- types over Γ are types with a "projection" (aka surjection) to Γ
    PSTy[_] : PresheafCategory C ℓ'' .ob → Type _
    PSTy[ Γ ] = Σ[ ΓA ∈ PresheafCategory C ℓ'' .ob ]
                   Σ[ π ∈ ΓA ⇒ Γ ]
                     (∀ (c : C .ob) → isSurjSET {A = ΓA ⟅ c ⟆} {Γ ⟅ c ⟆} (π ⟦ c ⟧))

    -- just directly use types from above as context extensions
    PSCext : (Γ : _) → PSTy[ Γ ] → Σ[ ΓA ∈ PresheafCategory C ℓ'' .ob ] ΓA ⇒ Γ
    PSCext Γ (ΓA , π , _) = ΓA , π

    -- the pullback or reindexed set is the disjoint union of the fibers
    -- from the projection
    module _ {Δ Γ : PresheafCategory C ℓ'' .ob} (γ : Δ ⇒ Γ)
             (A'@(ΓA , π , isSurjπ) : PSTy[ Γ ]) where
      ΔA : PresheafCategory C ℓ'' .ob
      ΔA .F-ob c =  ΔATy , isSetΔA
        where
          ΔATy = (Σ[ x ∈ fst (Δ ⟅ c ⟆) ] fiber (π ⟦ c ⟧) ((γ ⟦ c ⟧) x))

          isSetΔA : isSet ΔATy
          isSetΔA = isOfHLevelΣ 2 (snd (Δ ⟅ c ⟆)) λ Γc → isOfHLevelΣ 2 (snd (ΓA ⟅ c ⟆)) λ ΓAc → isProp→isSet (snd (Γ ⟅ c ⟆) _ _)
      -- for morphisms, we apply Δ ⟪ f ⟫ to the first component
      -- and ΓA ⟪ f ⟫ to the second
      -- the fiber rule
      ΔA .F-hom {c} {d} f (δax , γax , eq)
        = ((Δ ⟪ f ⟫) δax)
        , (((ΓA ⟪ f ⟫) γax)
        , ((π ⟦ d ⟧) ((ΓA ⟪ f ⟫) γax)
        ≡[ i ]⟨ π .N-hom f i γax ⟩
          (Γ ⟪ f ⟫) ((π ⟦ c ⟧) γax)
        ≡[ i ]⟨ (Γ ⟪ f ⟫) (eq i) ⟩
          (Γ ⟪ f ⟫) ((γ ⟦ c ⟧) δax)
        ≡[ i ]⟨ γ .N-hom f (~ i) δax ⟩
          (γ ⟦ d ⟧) ((Δ ⟪ f ⟫) δax)
        ∎))
      ΔA .F-id {x = c}
        = funExt λ (δax , γax , eq)
                → ΣPathP ((λ i → Δ .F-id i δax)
                          , fibersEqIfRepsEq {isSetB = snd (Γ ⟅ c ⟆)} _
                                            (λ i → ΓA .F-id i γax))
      ΔA .F-seq {a} {b} {c} f g
        = funExt λ (δax , γax , eq)
                → ΣPathP ((λ i → Δ .F-seq f g i δax)
                  , fibersEqIfRepsEq {isSetB = snd (Γ ⟅ c ⟆)} _
                                      λ i → ΓA .F-seq f g i γax)
      π' : ΔA ⇒ Δ
      π' .N-ob c (x , snd) = x
      π' .N-hom f = refl
      PSReindex : PSTy[ Δ ]
      PSReindex = ΔA , (π' , isSurj)
        where

          isSurj : ∀ (c : C .ob) → isSurjSET {A = ΔA ⟅ c ⟆} {B = Δ ⟅ c ⟆} (π' ⟦ c ⟧)
          isSurj c δx = (δx , isSurjπ c ((γ ⟦ c ⟧) δx)) , refl

      PSq : ΔA ⇒ ΓA
      PSq .N-ob c (δax , γax , eq) = γax
      PSq .N-hom {c} {d} f = funExt λ (δax , γax , eq) → refl

      PSSq : (PresheafCategory C ℓ'' ⋆ snd (PSCext Δ (PSReindex))) γ ≡
             (PresheafCategory C ℓ'' ⋆ PSq) (snd (PSCext Γ A'))
      PSSq = makeNatTransPath (funExt sqExt)
        where
          sqExt : ∀ (c : C .ob) → _
          sqExt c = funExt λ (δax , γax , eq) → sym eq

      PSIsPB : isPullback (PresheafCategory C ℓ'')
                 (cospan Δ Γ (fst (PSCext Γ A')) γ (snd (PSCext Γ A')))
                 (snd (PSCext Δ PSReindex)) PSq PSSq
      PSIsPB {Θ} p₁ p₂ sq = (α , eq) , unique
        where
          α : Θ ⇒ ΔA
          α .N-ob c t = ((p₁ ⟦ c ⟧) t)
                      , (((p₂ ⟦ c ⟧) t)
                      , (λ i → (sq (~ i) ⟦ c ⟧) t))
          α .N-hom {d} {c} f = funExt αHomExt
            where
              αHomExt : ∀ (t : fst (Θ ⟅ d ⟆))
                      → ((p₁ ⟦ c ⟧) ((Θ ⟪ f ⟫) t) , (p₂ ⟦ c ⟧) ((Θ ⟪ f ⟫) t), _)
                      ≡ ((Δ ⟪ f ⟫) ((p₁ ⟦ d ⟧) t) , (ΓA ⟪ f ⟫) ((p₂ ⟦ d ⟧) t) , _)
              αHomExt t = ΣPathP ((λ i → p₁ .N-hom f i t)
                                 , fibersEqIfRepsEq {isSetB = snd (Γ ⟅ c ⟆)} _
                                                    (λ i → p₂ .N-hom f i t))

          eq : _
          eq = makeNatTransPath (funExt (λ _ → funExt λ _ → refl))
             , makeNatTransPath (funExt (λ _ → funExt λ _ → refl))

          unique : ∀ (βeq : Σ[ β ∈ Θ ⇒ ΔA ] _)
                 → (α , eq) ≡ βeq
          unique (β , eqβ) = ΣPathP (α≡β , eq≡eqβ)
            where
              α≡β : α ≡ β
              α≡β = makeNatTransPath (funExt λ c → funExt λ t → eqExt c t)
                where
                  eqβ1 = eqβ .fst
                  eqβ2 = eqβ .snd
                  eqExt : ∀ (c : C .ob)
                        → (t : fst (Θ ⟅ c ⟆))
                        → (α ⟦ c ⟧) t ≡ (β ⟦ c ⟧) t
                  eqExt c t = ΣPathP ((λ i → (eqβ1 i ⟦ c ⟧) t)
                            , fibersEqIfRepsEq {isSetB = snd (Γ ⟅ c ⟆)} _
                                               (λ i → (eqβ2 i ⟦ c ⟧) t))
              eq≡eqβ : PathP (λ i
                             → (p₁ ≡ (α≡β i) ●ᵛ π')
                             × (p₂ ≡ (α≡β i) ●ᵛ PSq)) eq eqβ
              eq≡eqβ = ΣPathP ( isPropNatP1 (eq .fst) (eqβ .fst) α≡β
                              , isPropNatP2 (eq .snd) (eqβ .snd) α≡β)
                where
                  isPropNatP1 : isOfHLevelDep 1 (λ γ → p₁ ≡ γ ●ᵛ π')
                  isPropNatP1 = isOfHLevel→isOfHLevelDep 1 (λ _ → isSetNatTrans _ _)

                  isPropNatP2 : isOfHLevelDep 1 (λ γ → p₂ ≡ γ ●ᵛ PSq)
                  isPropNatP2 = isOfHLevel→isOfHLevelDep 1 (λ _ → isSetNatTrans _ _)

  -- putting everything together
  isTypeCategoryPresheaf : isTypeCategory (PresheafCategory C ℓ'')
  isTypeCategoryPresheaf .Ty[_] Γ = PSTy[ Γ ]
  isTypeCategoryPresheaf .cext = PSCext
  isTypeCategoryPresheaf .reindex = PSReindex
  isTypeCategoryPresheaf .q⟨_,_⟩ = PSq
  isTypeCategoryPresheaf .sq = PSSq
  isTypeCategoryPresheaf .isPB = PSIsPB

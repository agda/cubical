{-# OPTIONS --cubical --no-import-sorts --postfix-projections --safe #-}

module Cubical.Categories.TypeCategory where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
-- open import Cubical.HITs.PropositionalTruncation

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Limits.Pullback
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Sets

-- private
--   variable
--     ℓ ℓ' ℓ'' : Level

record isTypeCategory {ℓ ℓ' ℓ''} (C : Precategory ℓ ℓ')
       : Type (ℓ-max ℓ (ℓ-max ℓ' (ℓ-suc ℓ''))) where
  open Precategory C
  open Cospan
  open PullbackLegs
  open isPullback
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


    isPB : ∀ {Γ Γ' : ob} {A : Ty[ Γ ]} {f : C [ Γ' , Γ ]}
         → isPullback {C = C} (cospan Γ' Γ (Γ ⍮ A) f (π Γ A))
                      (pblegs (π Γ' (reindex f A)) q⟨ f , A ⟩)

-- presheaves are type contexts

module _ {ℓ ℓ' : Level} (C : Precategory ℓ ℓ') where
  open isTypeCategory
  open Precategory
  open Functor
  open NatTrans
  open isPullback

  private
    -- types over Γ are types with a "projection" (aka surjection) to Γ
    PSTy[_] : PreShv C .ob → Type _
    PSTy[ Γ ] = Σ[ ΓA ∈ PreShv C .ob ]
                   Σ[ π ∈ ΓA ⇒ Γ ]
                     (∀ (c : C .ob)
                     → isSurjSET {A = ΓA ⟅ c ⟆} {Γ ⟅ c ⟆} (π ⟦ c ⟧))

    -- just directly use types from above as context extensions
    PSCext : (Γ : _) → PSTy[ Γ ] → Σ[ ΓA ∈ PreShv C .ob ] ΓA ⇒ Γ
    PSCext Γ (ΓA , π , _) = ΓA , π

    -- the pullback or reindexed set is the disjoint union of the fibers
    -- from the projection
    module _ {Δ Γ : PreShv C .ob} (γ : Δ ⇒ Γ)
             (A'@(ΓA , π , isSurjπ) : PSTy[ Γ ]) where
      ΔA : PreShv C .ob
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
      PSReindex : PSTy[ Δ ]
      PSReindex = ΔA , (π' , isSurj)
        where
          π' : ΔA ⇒ Δ
          π' .N-ob c (x , snd) = x
          π' .N-hom f = refl

          isSurj : ∀ (c : C .ob) → isSurjSET {A = ΔA ⟅ c ⟆} {B = Δ ⟅ c ⟆} (π' ⟦ c ⟧)
          isSurj c δx = (δx , isSurjπ c ((γ ⟦ c ⟧) δx)) , refl

      PSq : ΔA ⇒ ΓA
      PSq .N-ob c (δax , γax , eq) = γax
      PSq .N-hom {c} {d} f = funExt λ (δax , γax , eq) → refl

      -- PSIsPB : isPullback
      --            (cospan Δ Γ (fst (PSCext Γ A')) γ (snd (PSCext Γ A')))
      --            (pblegs (snd (PSCext Δ PSReindex)) (PSq))
      -- PSIsPB = {!!}

  isTypeCategoryPresheaf : isTypeCategory (PreShv C)
  isTypeCategoryPresheaf .Ty[_] Γ = PSTy[ Γ ]

  isTypeCategoryPresheaf .cext = PSCext
  isTypeCategoryPresheaf .reindex = PSReindex
  isTypeCategoryPresheaf .q⟨_,_⟩ = PSq
  isTypeCategoryPresheaf .isPB .sq = makeNatTransPath (funExt sqExt)
    where
      sqExt : ∀ (c : C .ob) → _
      sqExt c = funExt λ (δax , γax , eq) → sym eq

  isTypeCategoryPresheaf .isPB .up pb' = ? , ?
  -- q⟨ isTypeCategoryPresheaf , γ ⟩ (ΓA , π , isSurj) = {!!}
    -- where
    --   ΔA = 
    -- where
    --   ΔA = 

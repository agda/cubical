{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Constructions.Fiber where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv.Base
open import Cubical.Categories.Category.Base
open Category
open import Cubical.Categories.Functor.Base
open Functor
open import Cubical.Categories.Displayed.Base
open Categoryᴰ
open import Cubical.Categories.Constructions.TotalCategory.Base
open import Cubical.Categories.Constructions.TotalCategory.Properties as TC

private
  variable
    ℓC ℓC' ℓD ℓD' : Level
    C : Category ℓC ℓC'
    D : Category ℓD ℓD'
    F : Functor C D

module _ {ℓC ℓC' ℓD ℓD'} {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} (F : Functor C D) where
  FiberCᴰ-Hom : ∀ {d d' : D .ob} (δ : D [ d , d' ]) → fiber (F .F-ob) d → fiber (F .F-ob) d' → Type (ℓ-max ℓC' ℓD')
  FiberCᴰ-Hom {d} {d'} δ (c , eq) (c' , eq') = Σ[ γ ∈ C [ c , c' ] ] PathP (λ i → D [ eq i , eq' i ]) (F .F-hom γ) δ

  FiberCᴰ-HomPathP :  ∀ {d d' : D .ob} {δ1 δ2 : D [ d , d' ]} (eδ : δ1 ≡ δ2) →
    (c/d : fiber (F .F-ob) d) → (c'/d' : fiber (F .F-ob) d') →
    (γ1/δ1 : FiberCᴰ-Hom δ1 c/d c'/d') →
    (γ2/δ2 : FiberCᴰ-Hom δ2 c/d c'/d') →
    (fst γ1/δ1 ≡ fst γ2/δ2) → PathP (λ i → FiberCᴰ-Hom (eδ i) c/d c'/d') γ1/δ1 γ2/δ2
  FiberCᴰ-HomPathP {d}{d'} {δ1}{δ2} eδ (c , c↦d) (c' , c'↦d') (γ1 , γ1↦δ1) (γ2 , γ2↦δ2) eγ =
    congP₂ (λ i → _,_) eγ (fst (isOfHLevelPathP' 0 (isOfHLevelPathP' 1 (isSetHom D) _ _) γ1↦δ1 γ2↦δ2))

  FiberCᴰ : Categoryᴰ D (ℓ-max ℓC ℓD) (ℓ-max ℓC' ℓD')
  ob[ FiberCᴰ ] d = fiber (F .F-ob) d
  Hom[_][_,_] FiberCᴰ {d} {d'} δ (c , eq) (c' , eq') = FiberCᴰ-Hom {d} {d'} δ (c , eq) (c' , eq')
  idᴰ FiberCᴰ {d} {c , c↦d} = id C , subst
    (λ δ → PathP (λ i → D [ c↦d i , c↦d i ]) δ (id D))
    (sym (F .F-id))
    λ i → id D
  _⋆ᴰ_ FiberCᴰ {d}{d'}{d''} {δ1}{δ2} {c , c↦d} {c' , c'↦d'} {c'' , c''↦d''} (γ1 , γ1↦δ1) (γ2 , γ2↦δ2) =
    (γ1 ⋆⟨ C ⟩ γ2) , subst
    (λ δ → PathP (λ i → D [ c↦d i , c''↦d'' i ]) δ (δ1 ⋆⟨ D ⟩ δ2))
    (sym (F .F-seq γ1 γ2))
    λ i → γ1↦δ1 i ⋆⟨ D ⟩ γ2↦δ2 i
  ⋆IdLᴰ FiberCᴰ {d}{d'}{δ}{c , c↦d}{c' , c'↦d'} (γ , γ↦δ) =
    FiberCᴰ-HomPathP (⋆IdL D δ) _ _ _ _ (⋆IdL C γ)
  ⋆IdRᴰ FiberCᴰ {d}{d'}{δ}{c , c↦d}{c' , c'↦d'} (γ , γ↦δ) =
    FiberCᴰ-HomPathP (⋆IdR D δ) _ _ _ _ (⋆IdR C γ)
  ⋆Assocᴰ FiberCᴰ (γ1 , _) (γ2 , _) (γ3 , _) =
    FiberCᴰ-HomPathP (⋆Assoc D _ _ _) _ _ _ _ (⋆Assoc C γ1 γ2 γ3)
  isSetHomᴰ FiberCᴰ {f = δ} = isSetΣ
    (isSetHom C)
    (λ c → isOfHLevelPathP' 2 (isSet→isGroupoid (isSetHom D)) (F .F-hom c) δ)

  ∫FiberC : Category (ℓ-max ℓC ℓD) (ℓ-max ℓC' ℓD')
  ∫FiberC = ∫C FiberCᴰ

  FiberCod : Functor ∫FiberC D
  FiberCod = TC.Fst {C = D} {FiberCᴰ}

  FiberDom : Functor ∫FiberC C
  F-ob FiberDom (d , c , c↦d) = c
  F-hom FiberDom (δ , γ , γ↦δ) = γ
  F-id FiberDom = refl
  F-seq FiberDom _ _ = refl

  fiberFactors : funcComp F FiberDom ≡ FiberCod
  fiberFactors = Functor≡
    (λ (d , c , c↦d) → c↦d)
    λ {(d , c , c↦d)} {(d' , c' , c'↦d')} (δ , γ , γ↦δ) → γ↦δ

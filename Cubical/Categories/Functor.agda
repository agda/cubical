{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Categories.Functor where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Categories.Category

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

record Functor (C : Precategory ℓC ℓC') (D : Precategory ℓD ℓD') : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where
  no-eta-equality
  open Precategory

  field
    F-ob : C .ob → D .ob
    F-hom : {x y : C .ob} → C [ x , y ] → D [(F-ob x) , (F-ob y)]
    F-id : {x : C .ob} → F-hom (C .id x) ≡ D .id (F-ob x)
    F-seq : {x y z : C .ob} (f : C [ x , y ]) (g : C [ y , z ]) → F-hom (f ⋆⟨ C ⟩ g) ≡ (F-hom f) ⋆⟨ D ⟩ (F-hom g)

  isFull = (x y : _) (F[f] : D [(F-ob x) , (F-ob y)]) → ∃ (C [ x , y ]) (λ f → F-hom f ≡ F[f])
  isFaithful = (x y : _) (f g : C [ x , y ]) → F-hom f ≡ F-hom g → f ≡ g

private
  variable
    ℓE ℓE' : Level
    C : Precategory ℓC ℓC'
    D : Precategory ℓD ℓD'
    E : Precategory ℓE ℓE'

open Precategory
open Functor

-- Helpful notation

-- action on objects
_⟅_⟆ : (F : Functor C D)
     → C .ob
     → D .ob
_⟅_⟆ = F-ob

-- action on morphisms
_⟪_⟫ : (F : Functor C D)
     → ∀ {x y}
     → C [ x , y ]
     → D [(F ⟅ x ⟆) , (F ⟅ y ⟆)]
_⟪_⟫ = F-hom


-- Functor results

-- functor composition
funcComp : ∀ (F : Functor C D) (G : Functor D E) → Functor C E
(funcComp F G) .F-ob c = G ⟅ F ⟅ c ⟆ ⟆
(funcComp F G) .F-hom f = G ⟪ F ⟪ f ⟫ ⟫
(funcComp {C = C} {D = D} {E = E} F G) .F-id {c}
  = (G ⟪ F ⟪ C .id c ⟫ ⟫)
  ≡⟨ cong (G ⟪_⟫) (F .F-id) ⟩
    (G ⟪ D .id (F ⟅ c ⟆) ⟫)
  ≡⟨ G .F-id ⟩
    E .id (G ⟅ F ⟅ c ⟆ ⟆)
  ∎
(funcComp {C = C} {D = D} {E = E} F G) .F-seq {x} {y} {z} f g
  = (G ⟪ F ⟪ f ⋆⟨ C ⟩ g ⟫ ⟫)
  ≡⟨ cong (G ⟪_⟫) (F .F-seq _ _) ⟩
    (G ⟪ (F ⟪ f ⟫) ⋆⟨ D ⟩ (F ⟪ g ⟫) ⟫)
  ≡⟨ G .F-seq _ _ ⟩
    (G ⟪ F ⟪ f ⟫ ⟫) ⋆⟨ E ⟩ (G ⟪ F ⟪ g ⟫ ⟫)
  ∎

-- functors preserve isomorphisms
preserveIsosF : ∀ {x y} (F : Functor C D) → CatIso {C = C} x y → CatIso {C = D} (F ⟅ x ⟆) (F ⟅ y ⟆)
preserveIsosF {C = C} {D = D} {x} {y} F (catiso f f⁻¹ sec' ret') =
  catiso
    g g⁻¹
    -- sec
    ( (g⁻¹ ⋆⟨ D ⟩ g)
    ≡⟨ sym (F .F-seq f⁻¹ f) ⟩
      F ⟪ f⁻¹ ⋆⟨ C ⟩ f ⟫
    ≡⟨ cong (F .F-hom) sec' ⟩
      F ⟪ C .id y ⟫
    ≡⟨ F .F-id ⟩
      D .id y'
    ∎ )
    -- ret
    ( (g ⋆⟨ D ⟩ g⁻¹)
      ≡⟨ sym (F .F-seq f f⁻¹) ⟩
    F ⟪ f ⋆⟨ C ⟩ f⁻¹ ⟫
      ≡⟨ cong (F .F-hom) ret' ⟩
    F ⟪ C .id x ⟫
    ≡⟨ F .F-id ⟩
      D .id x'
    ∎ )

    where
      x' : D .ob
      x' = F ⟅ x ⟆
      y' : D .ob
      y' = F ⟅ y ⟆

      g : D [ x' , y' ]
      g = F ⟪ f ⟫
      g⁻¹ : D [ y' , x' ]
      g⁻¹ = F ⟪ f⁻¹ ⟫

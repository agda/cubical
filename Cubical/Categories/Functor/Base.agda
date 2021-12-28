{-# OPTIONS --safe #-}
module Cubical.Categories.Functor.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma

open import Cubical.Categories.Category

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

record Functor (C : Category ℓC ℓC') (D : Category ℓD ℓD') :
         Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where
  no-eta-equality

  open Category

  field
    F-ob  : C .ob → D .ob
    F-hom : {x y : C .ob} → C [ x , y ] → D [ F-ob x , F-ob y ]
    F-id  : {x : C .ob} → F-hom (C .id) ≡ D .id {x = F-ob x}
    F-seq : {x y z : C .ob} (f : C [ x , y ]) (g : C [ y , z ])
          → F-hom (f ⋆⟨ C ⟩ g) ≡ (F-hom f) ⋆⟨ D ⟩ (F-hom g)

  isFull = (x y : _) (F[f] : D [ F-ob x , F-ob y ]) → ∃[ f ∈ C [ x , y ] ] F-hom f ≡ F[f]
  isFaithful = (x y : _) (f g : C [ x , y ]) → F-hom f ≡ F-hom g → f ≡ g
  isEssentiallySurj = (d : D .ob) → Σ[ c ∈ C .ob ] CatIso D (F-ob c) d

private
  variable
    ℓ ℓ' : Level
    C D E : Category ℓ ℓ'

open Category
open Functor

-- Helpful notation

-- action on objects
infix 30 _⟅_⟆
_⟅_⟆ : (F : Functor C D)
     → C .ob
     → D .ob
_⟅_⟆ = F-ob

-- action on morphisms
infix 30 _⟪_⟫ -- same infix level as on objects since these will never be used in the same context
_⟪_⟫ : (F : Functor C D)
     → ∀ {x y}
     → C [ x , y ]
     → D [(F ⟅ x ⟆) , (F ⟅ y ⟆)]
_⟪_⟫ = F-hom


-- Functor constructions

𝟙⟨_⟩ : ∀ (C : Category ℓ ℓ') → Functor C C
𝟙⟨ C ⟩ .F-ob x    = x
𝟙⟨ C ⟩ .F-hom f   = f
𝟙⟨ C ⟩ .F-id      = refl
𝟙⟨ C ⟩ .F-seq _ _ = refl

-- functor composition
funcComp : ∀ (G : Functor D E) (F : Functor C D) → Functor C E
(funcComp G F) .F-ob c    = G ⟅ F ⟅ c ⟆ ⟆
(funcComp G F) .F-hom f   = G ⟪ F ⟪ f ⟫ ⟫
(funcComp G F) .F-id      = cong (G ⟪_⟫) (F .F-id) ∙ G .F-id
(funcComp G F) .F-seq f g = cong (G ⟪_⟫) (F .F-seq _ _) ∙ G .F-seq _ _

infixr 30 funcComp
syntax funcComp G F = G ∘F F

_^opF : Functor C D → Functor (C ^op) (D ^op)
(F ^opF) .F-ob      = F .F-ob
(F ^opF) .F-hom     = F .F-hom
(F ^opF) .F-id      = F .F-id
(F ^opF) .F-seq f g = F .F-seq g f

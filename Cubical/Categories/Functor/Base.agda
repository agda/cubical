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

  -- preservation of commuting squares and triangles
  F-square : {x y u v : C .ob}
             {f : C [ x , y ]} {g : C [ x , u ]}
             {h : C [ u , v ]} {k : C [ y , v ]}
           → f ⋆⟨ C ⟩ k ≡ g ⋆⟨ C ⟩ h
           → (F-hom f) ⋆⟨ D ⟩ (F-hom k) ≡ (F-hom g) ⋆⟨ D ⟩ (F-hom h)
  F-square Csquare = sym (F-seq _ _) ∙∙ cong F-hom Csquare ∙∙ F-seq _ _

  F-triangle : {x y z : C .ob}
               {f : C [ x , y ]} {g : C [ y , z ]} {h : C [ x , z ]}
             → f ⋆⟨ C ⟩ g ≡ h
             → (F-hom f) ⋆⟨ D ⟩ (F-hom g) ≡ (F-hom h)
  F-triangle Ctriangle = sym (F-seq _ _) ∙ cong F-hom Ctriangle

private
  variable
    ℓ ℓ' : Level
    C D E : Category ℓ ℓ'

open Category
open Functor

Functor≡ : {F G : Functor C D}
         → (h : ∀ (c : ob C) → F-ob F c ≡ F-ob G c)
         → (∀ {c c' : ob C} (f : C [ c , c' ]) → PathP (λ i → D [ h c i , h c' i ]) (F-hom F f) (F-hom G f))
         → F ≡ G
F-ob (Functor≡ hOb hHom i) c = hOb c i
F-hom (Functor≡ hOb hHom i) f = hHom f i
F-id (Functor≡ {C = C} {D = D} {F = F} {G = G} hOb hHom i) =
  isProp→PathP (λ j → isSetHom D (hHom (C .id) j) (D .id)) (F-id F) (F-id G) i
F-seq (Functor≡ {C = C} {D = D} {F = F} {G = G} hOb hHom i) f g =
  isProp→PathP (λ j → isSetHom D (hHom (f ⋆⟨ C ⟩ g) j) ((hHom f j) ⋆⟨ D ⟩ (hHom g j))) (F-seq F f g) (F-seq G f g) i



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

{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Categories.Functor where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws using (lUnit; rUnit; assoc; cong-∙)
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
  isEssentiallySurj = ∀ (d : D .ob) → Σ[ c ∈ C .ob ] CatIso {C = D} (F-ob c) d

private
  variable
    ℓ ℓ' ℓ'' : Level
    ℓE ℓE' : Level
    B : Precategory ℓC ℓC'
    C : Precategory ℓC ℓC'
    D : Precategory ℓD ℓD'
    E : Precategory ℓE ℓE'

open Precategory
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

𝟙⟨_⟩ : ∀ (C : Precategory ℓ ℓ') → Functor C C
𝟙⟨ C ⟩ .F-ob x = x
𝟙⟨ C ⟩ .F-hom f = f
𝟙⟨ C ⟩ .F-id = refl
𝟙⟨ C ⟩ .F-seq _ _ = refl

-- functor composition
funcComp : ∀ (G : Functor D E) (F : Functor C D) → Functor C E
(funcComp G F) .F-ob c = G ⟅ F ⟅ c ⟆ ⟆
(funcComp G F) .F-hom f = G ⟪ F ⟪ f ⟫ ⟫
(funcComp {D = D} {E = E} {C = C} G F) .F-id {c}
  = (G ⟪ F ⟪ C .id c ⟫ ⟫)
  ≡⟨ cong (G ⟪_⟫) (F .F-id) ⟩
    G .F-id
  --   (G ⟪ D .id (F ⟅ c ⟆) ⟫) -- deleted this cause the extra refl composition was annoying
  -- ≡⟨ G .F-id ⟩
  --   E .id (G ⟅ F ⟅ c ⟆ ⟆)
  -- ∎
(funcComp {D = D} {E = E} {C = C} G F) .F-seq {x} {y} {z} f g
  = (G ⟪ F ⟪ f ⋆⟨ C ⟩ g ⟫ ⟫)
  ≡⟨ cong (G ⟪_⟫) (F .F-seq _ _) ⟩
    G .F-seq _ _
  --   (G ⟪ (F ⟪ f ⟫) ⋆⟨ D ⟩ (F ⟪ g ⟫) ⟫) -- deleted for same reason as above
  -- ≡⟨ G .F-seq _ _ ⟩
  --   (G ⟪ F ⟪ f ⟫ ⟫) ⋆⟨ E ⟩ (G ⟪ F ⟪ g ⟫ ⟫)
  -- ∎

infixr 30 funcComp
syntax funcComp G F = G ∘F F

infixr 15 _◍_
-- is there actual function composition in the library somewhere?
_◍_ : ∀ {X : Type ℓ} {Y : Type ℓ'} {Z : Type ℓ''} → (Y → Z) → (X → Y) → (X → Z)
(g ◍ f) x = g (f x)

congAssoc : ∀ {X : Type ℓ} {Y : Type ℓ'} {Z : Type ℓ''} (g : X → Y) (h : Y → Z) {x x' : X} {y : Y} {z : Z}
          → (p : x ≡ x') (q : g x' ≡ y) (r : h y ≡ z)
          → cong (h ◍ g) p ∙ (cong h q ∙ r) ≡ cong h (cong g p ∙ q) ∙ r
congAssoc g h p q r
  = cong (h ◍ g) p ∙ (cong h q ∙ r)
  ≡⟨ assoc _ _ _ ⟩
    ((cong (h ◍ g) p) ∙ (cong h q)) ∙ r
  ≡⟨ refl ⟩
    (cong h (cong g p) ∙ (cong h q)) ∙ r
  ≡⟨ cong (_∙ r) (sym (cong-∙ h _ _)) ⟩
    cong h (cong g p ∙ q) ∙ r
  ∎

-- composition is associative
F-assoc : {F : Functor B C} {G : Functor C D} {H : Functor D E}
        → H ∘F (G ∘F F) ≡ (H ∘F G) ∘F F
F-assoc {F = F} {G} {H} i .F-ob x = H ⟅ G ⟅ F ⟅ x ⟆ ⟆ ⟆
F-assoc {F = F} {G} {H} i .F-hom f = H ⟪ G ⟪ F ⟪ f ⟫ ⟫ ⟫
F-assoc {F = F} {G} {H} i .F-id {x} =  congAssoc (G ⟪_⟫) (H ⟪_⟫) (F .F-id {x}) (G .F-id {F ⟅ x ⟆}) (H .F-id) (~ i)
F-assoc {F = F} {G} {H} i .F-seq f g =  congAssoc (G ⟪_⟫) (H ⟪_⟫) (F .F-seq f g) (G .F-seq _ _) (H .F-seq _ _) (~ i)

-- Results about functors

module _ {C : Precategory ℓC ℓC'} {D : Precategory ℓD ℓD'} {F : Functor C D} where

  -- the identity is the identity
  F-lUnit : F ∘F 𝟙⟨ C ⟩ ≡ F
  F-lUnit i .F-ob x = F ⟅ x ⟆
  F-lUnit i .F-hom f = F ⟪ f ⟫
  F-lUnit i .F-id {x} = lUnit (F .F-id) (~ i)
  F-lUnit i .F-seq f g = lUnit (F .F-seq f g) (~ i)

  F-rUnit : 𝟙⟨ D ⟩ ∘F F  ≡ F
  F-rUnit i .F-ob x = F ⟅ x ⟆
  F-rUnit i .F-hom f = F ⟪ f ⟫
  F-rUnit i .F-id {x} = rUnit (F .F-id) (~ i)
  F-rUnit i .F-seq f g = rUnit (F .F-seq f g) (~ i)

  -- functors preserve commutative diagrams (specificallysqures here)
  preserveCommF : ∀ {x y z w} {f : C [ x , y ]} {g : C [ y , w ]} {h : C [ x , z ]} {k : C [ z , w ]}
                → f ⋆⟨ C ⟩ g ≡ h ⋆⟨ C ⟩ k
                → (F ⟪ f ⟫) ⋆⟨ D ⟩ (F ⟪ g ⟫) ≡ (F ⟪ h ⟫) ⋆⟨ D ⟩ (F ⟪ k ⟫)
  preserveCommF {f = f} {g = g} {h = h} {k = k} eq
    = (F ⟪ f ⟫) ⋆⟨ D ⟩ (F ⟪ g ⟫)
    ≡⟨ sym (F .F-seq _ _) ⟩
      F ⟪ f ⋆⟨ C ⟩ g ⟫
    ≡⟨ cong (F ⟪_⟫) eq ⟩
      F ⟪ h ⋆⟨ C ⟩ k ⟫
    ≡⟨ F .F-seq _ _ ⟩
      (F ⟪ h ⟫) ⋆⟨ D ⟩ (F ⟪ k ⟫)
    ∎

  -- functors preserve isomorphisms
  preserveIsosF : ∀ {x y} → CatIso {C = C} x y → CatIso {C = D} (F ⟅ x ⟆) (F ⟅ y ⟆)
  preserveIsosF {x} {y} (catiso f f⁻¹ sec' ret') =
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


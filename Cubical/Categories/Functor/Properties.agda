{-# OPTIONS --safe #-}

module Cubical.Categories.Functor.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function renaming (_∘_ to _◍_)
open import Cubical.Foundations.GroupoidLaws using (lUnit; rUnit; assoc; cong-∙)
open import Cubical.Foundations.HLevels
open import Cubical.Categories.Category
open import Cubical.Categories.Functor.Base


private
  variable
    ℓ ℓ' ℓ'' : Level
    B C D E : Category ℓ ℓ'

open Category
open Functor

{-
x ---p--- x'
         ⇓ᵍ
       g x' ---q--- y
                   ⇓ʰ
                 h y ---r--- z

The path from `h (g x) ≡ z` obtained by
  1. first applying cong to p and composing with q; then applying cong again and composing with r
  2. first applying cong to q and composing with r; then applying a double cong to p and precomposing
are path equal.
-}
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

module _ {F : Functor C D} where

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
  preserveIsosF : ∀ {x y} → CatIso C x y → CatIso D (F ⟅ x ⟆) (F ⟅ y ⟆)
  preserveIsosF {x} {y} (catiso f f⁻¹ sec' ret') =
    catiso
      g g⁻¹
      -- sec
      ( (g⁻¹ ⋆⟨ D ⟩ g)
      ≡⟨ sym (F .F-seq f⁻¹ f) ⟩
        F ⟪ f⁻¹ ⋆⟨ C ⟩ f ⟫
      ≡⟨ cong (F .F-hom) sec' ⟩
        F ⟪ C .id ⟫
      ≡⟨ F .F-id ⟩
        D .id
      ∎ )
      -- ret
      ( (g ⋆⟨ D ⟩ g⁻¹)
        ≡⟨ sym (F .F-seq f f⁻¹) ⟩
      F ⟪ f ⋆⟨ C ⟩ f⁻¹ ⟫
        ≡⟨ cong (F .F-hom) ret' ⟩
      F ⟪ C .id ⟫
      ≡⟨ F .F-id ⟩
        D .id
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


isSetFunctor : isSet (D .ob) → isSet (Functor C D)
isSetFunctor {D = D} {C = C} isSet-D-ob F G p q = w
  where
    w : _
    F-ob (w i i₁) = isSetΠ (λ _ → isSet-D-ob) _ _ (cong F-ob p) (cong F-ob q) i i₁
    F-hom (w i i₁) z =
     isSet→SquareP
       (λ i i₁ → D .isSetHom {(F-ob (w i i₁) _)} {(F-ob (w i i₁) _)})
        (λ i₁ → F-hom (p i₁) z) (λ i₁ → F-hom (q i₁) z) refl refl i i₁

    F-id (w i i₁) =
       isSet→SquareP
       (λ i i₁ → isProp→isSet (D .isSetHom (F-hom (w i i₁) _) (D .id)))
       (λ i₁ → F-id (p i₁)) (λ i₁ → F-id (q i₁)) refl refl i i₁

    F-seq (w i i₁) _ _ =
     isSet→SquareP
       (λ i i₁ → isProp→isSet (D .isSetHom (F-hom (w i i₁) _) ((F-hom (w i i₁) _) ⋆⟨ D ⟩ (F-hom (w i i₁) _))))
       (λ i₁ → F-seq (p i₁) _ _) (λ i₁ → F-seq (q i₁) _ _) refl refl i i₁


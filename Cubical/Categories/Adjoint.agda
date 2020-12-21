{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Categories.Adjoint where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Foundations.Isomorphism

open Functor

open Iso
open Precategory

private
  variable
    ℓC ℓC' ℓD ℓD' : Level
    C : Precategory ℓC ℓC'
    D : Precategory ℓD ℓD'
    -- c : C .ob
    -- d : D .ob

record Preadjoint {C : Precategory ℓC ℓC'} {D : Precategory ℓD ℓD'} (F : Functor C D) (G : Functor D C) : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where

-- AdjIso : {C : Precategory ℓC ℓC'} {D : Precategory ℓD ℓD'} (F : Functor C D) (G : Functor D C)
--        → Type _
  field
    adjIso : ∀ {c d} → Iso (D [ F ⟅ c ⟆ , d ]) (C [ c , G ⟅ d ⟆ ])

-- _♭ : ∀ {c d} {F : Functor C D} {G : Functor D C} ⦃ fgIso : AdjIso F G ⦄ → (D [ F ⟅ c ⟆ , d ]) → (C [ c , G ⟅ d ⟆ ])
-- (_♭) ⦃ fgIso ⦄ = fgIso .fun

  infix 40 _♭
  infix 40 _♯
  _♭ : ∀ {c d} → (D [ F ⟅ c ⟆ , d ]) → (C [ c , G ⟅ d ⟆ ])
  (_♭) {_} {_} = adjIso .fun

  _♯ : ∀ {c d} → (C [ c , G ⟅ d ⟆ ]) → (D [ F ⟅ c ⟆ , d ])
  (_♯) {_} {_} = adjIso .inv


record isAdjoint {C : Precategory ℓC ℓC'} {D : Precategory ℓD ℓD'} {F : Functor C D} {G : Functor D C}
                 (adj : Preadjoint F G)
                 : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where
  open Preadjoint adj
  field
    -- unit
    η : 𝟙⟨ C ⟩ ⇒ (funcComp G F)
    -- counit
    ε : (funcComp F G) ⇒ 𝟙⟨ D ⟩
    -- triangle identities
    Δ₁ : (F ∘ʳ η) ●ᵛ (ε ∘ˡ F) ≡ 1[ F ]


open isAdjoint


record isAdjoint2 {C : Precategory ℓC ℓC'} {D : Precategory ℓD ℓD'} {F : Functor C D} {G : Functor D C}
                 (adj : Preadjoint F G)
                 : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where
  open Preadjoint adj
  field
    -- Naturality conditions
    -- flatting (sharpening) is a natural in that it commutes with post (pre) composition
    adjNatInD : ∀ {c : C .ob} {d d'} (f : D [ F ⟅ c ⟆ , d ]) (k : D [ d , d' ])
              → (f ⋆⟨ D ⟩ k) ♭ ≡ f ♭ ⋆⟨ C ⟩ G ⟪ k ⟫

    adjNatInC : ∀ {c' c d} (g : C [ c , G ⟅ d ⟆ ]) (h : C [ c' , c ])
              → (h ⋆⟨ C ⟩ g) ♯ ≡ F ⟪ h ⟫ ⋆⟨ D ⟩ g ♯

open isAdjoint2

record isAdjoint3 {C : Precategory ℓC ℓC'} {D : Precategory ℓD ℓD'} {F : Functor C D} {G : Functor D C}
                 (adj : Preadjoint F G)
                 : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where
  open Preadjoint adj
  field
    adjNat' : ∀ {c c' d d'} {f : D [ F ⟅ c ⟆ , d ]} {k : D [ d , d' ]}
              → {h : C [ c , c' ]} {g : C [ c' , G ⟅ d' ⟆ ]}
              -- commutativity of squares is iff
              → ((f ⋆⟨ D ⟩ k ≡ F ⟪ h ⟫ ⋆⟨ D ⟩ g ♯) → (f ♭ ⋆⟨ C ⟩ G ⟪ k ⟫ ≡ h ⋆⟨ C ⟩ g))
              × ((f ♭ ⋆⟨ C ⟩ G ⟪ k ⟫ ≡ h ⋆⟨ C ⟩ g) → (f ⋆⟨ D ⟩ k ≡ F ⟪ h ⟫ ⋆⟨ D ⟩ g ♯))

open isAdjoint3


module _ {C : Precategory ℓC ℓC'} {D : Precategory ℓD ℓD'} (F : Functor C D) (G : Functor D C) (adj : Preadjoint F G) where
  open Preadjoint adj
  adj2→3 : isAdjoint2 adj
        → isAdjoint3 adj
  (adj2→3 isA2) .adjNat' {c} {c'} {d} {d'} {f} {k} {h} {g} = D→C , C→D
    where
      D→C : (f ⋆⟨ D ⟩ k ≡ F ⟪ h ⟫ ⋆⟨ D ⟩ g ♯) → (f ♭ ⋆⟨ C ⟩ G ⟪ k ⟫ ≡ h ⋆⟨ C ⟩ g)
      D→C eq = f ♭ ⋆⟨ C ⟩ G ⟪ k ⟫
             ≡⟨ sym (isA2 .adjNatInD _ _) ⟩
               ((f ⋆⟨ D ⟩ k) ♭)
             ≡⟨ cong _♭ eq ⟩
               (F ⟪ h ⟫ ⋆⟨ D ⟩ g ♯) ♭
             ≡⟨ sym (cong _♭ (isA2 .adjNatInC _ _)) ⟩
               (h ⋆⟨ C ⟩ g) ♯ ♭
             ≡⟨ adjIso .rightInv _ ⟩
               h ⋆⟨ C ⟩ g
             ∎
      C→D : (f ♭ ⋆⟨ C ⟩ G ⟪ k ⟫ ≡ h ⋆⟨ C ⟩ g) → (f ⋆⟨ D ⟩ k ≡ F ⟪ h ⟫ ⋆⟨ D ⟩ g ♯)
      C→D eq = f ⋆⟨ D ⟩ k
             ≡⟨ sym (adjIso .leftInv _) ⟩
               (f ⋆⟨ D ⟩ k) ♭ ♯
             ≡⟨ cong _♯ (isA2 .adjNatInD _ _) ⟩
               (f ♭ ⋆⟨ C ⟩ G ⟪ k ⟫) ♯
             ≡⟨ cong _♯ eq ⟩
               (h ⋆⟨ C ⟩ g) ♯
             ≡⟨ isA2 .adjNatInC _ _ ⟩
               F ⟪ h ⟫ ⋆⟨ D ⟩ g ♯
             ∎

  open NatTrans 
  adj3→1 : isAdjoint3 adj
         → isAdjoint adj
  (adj3→1 isA3) .η .N-ob x = (D .id _) ♭
  (adj3→1 isA3) .η .N-hom f = sym (fst (isA3 .adjNat') (commInD ∙ surround))
    where
      -- trivial commutative diagram between identities in D
      commInD : (D .id _) ⋆⟨ D ⟩ F ⟪ f ⟫ ≡ F ⟪ f ⟫ ⋆⟨ D ⟩ (D .id _)
      commInD = (D .⋆IdL _) ∙ sym (D .⋆IdR _)

      surround : F ⟪ f ⟫ ⋆⟨ D ⟩ (D .id _) ≡ F ⟪ f ⟫ ⋆⟨ D ⟩ (D .id _) ♭ ♯
      surround = cong (λ v → F ⟪ f ⟫ ⋆⟨ D ⟩ v) (sym (adjIso .leftInv _))
  (adj3→1 isA3) .ε .N-ob x = (C .id _) ♯
  (adj3→1 isA3) .ε .N-hom g = sym (snd (isA3 .adjNat') {!!})
    where
      -- trivial commutative diagram between identities in C
      commInC : (C .id _) ⋆⟨ C ⟩ G ⟪ g ⟫ ≡ G ⟪ g ⟫ ⋆⟨ C ⟩ (C .id _)
      commInC = (C .⋆IdL _) ∙ sym (C .⋆IdR _)

      surround : G ⟪ g ⟫ ⋆⟨ C ⟩ (C .id _) ≡ G ⟪ g ⟫ ⋆⟨ C ⟩ (C .id _) ♯ ♭
      surround = cong (λ v → G ⟪ g ⟫ ⋆⟨ C ⟩ v) (sym (adjIso .rightInv _))
      


-- record Adjoint' {C : Precategory ℓC ℓC'} {D : Precategory ℓD ℓD'} (F : Functor C D) (G : Functor D C) ⦃ fgIso : AdjIso F G ⦄ : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where
--   -- sharpening and flattening

--   field
--     -- Naturality conditions
--     -- flatting (sharpening) is a natural in that it commutes with post (pre) composition
--     adjNatInD : ∀ {c : C .ob} {d d'} (f : D [ F ⟅ c ⟆ , d ]) (k : D [ d , d' ])
--               → (f ⋆⟨ D ⟩ k) ♭ ≡ f ♭ ⋆⟨ C ⟩ G ⟪ k ⟫

--     adjNatInC : ∀ {c' c d} (g : C [ c , G ⟅ d ⟆ ]) (h : C [ c' , c ])
--               → (h ⋆⟨ C ⟩ g) ♯ ≡ F ⟪ h ⟫ ⋆⟨ D ⟩ g ♯

-- record Adjoint'' {C : Precategory ℓC ℓC'} {D : Precategory ℓD ℓD'} (F : Functor C D) (G : Functor D C) ⦃ fgIso : AdjIso F G ⦄ : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where
--   -- sharpening and flattening
--   _♭ : ∀ {c d} → (D [ F ⟅ c ⟆ , d ]) → (C [ c , G ⟅ d ⟆ ])
--   (_♭) {_} {_} = fgIso .fun

--   _♯ : ∀ {c d} → (C [ c , G ⟅ d ⟆ ]) → (D [ F ⟅ c ⟆ , d ])
--   (_♯) {_} {_} = fgIso .inv

--   field
--     adjNatD→C : ∀ {c c' d d'} {f : D [ F ⟅ c ⟆ , d ]} {k : D [ d , d' ]}
--               → {h : C [ c , c' ]} {g : C [ c' , G ⟅ d' ⟆ ]}
--               → (f ⋆⟨ D ⟩ k ≡ F ⟪ h ⟫ ⋆⟨ D ⟩ g ♯) → (f ♭ ⋆⟨ C ⟩ G ⟪ k ⟫ ≡ h ⋆⟨ C ⟩ g)

-- -- equivalent formulation of naturality


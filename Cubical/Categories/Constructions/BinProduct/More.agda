-- Product of two categories
{-# OPTIONS --safe #-}

module Cubical.Categories.Constructions.BinProduct.More where

open import Cubical.Categories.Constructions.BinProduct.Base

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Functors.More

open import Cubical.Tactics.CategorySolver.Reflection

private
  variable
    ℓC ℓC' ℓD ℓD' ℓE ℓE' : Level

open Category
open Functor

-- Some more functor combinators
Δ : ∀ (C : Category ℓC ℓC') → Functor C (C ×C C)
Δ C = Id ,F Id

-- helpful decomposition of morphisms used in several proofs
-- about product category
module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}{E : Category ℓE ℓE'} where

  BinMorphDecompL : ∀ {x1 x2} {y1 y2} ((f , g) : (C ×C D) [ (x1 , y1) ,
                                                            (x2 , y2) ])
                      → (F : Functor (C ×C D) E)
                      → (F ⟪ f , g ⟫) ≡
                           (F ⟪ f , D .id ⟫) ⋆⟨ E ⟩ (F ⟪ C .id , g ⟫)
  BinMorphDecompL (f , g) F =
    (F ⟪ f , g ⟫)
      ≡⟨ (λ i → F ⟪ C .⋆IdR f (~ i), D .⋆IdL g (~ i)⟫) ⟩
    (F ⟪ f ⋆⟨ C ⟩ C .id , D .id ⋆⟨ D ⟩ g ⟫)
      ≡⟨ F .F-seq (f , D .id) (C .id , g) ⟩
    (F ⟪ f , D .id ⟫) ⋆⟨ E ⟩ (F ⟪ C .id , g ⟫) ∎

  BinMorphDecompR : ∀ {x1 x2} {y1 y2} ((f , g) : (C ×C D) [ (x1 , y1) ,
                                                            (x2 , y2) ])
                      → (F : Functor (C ×C D) E)
                      → (F ⟪ f , g ⟫) ≡
                        (F ⟪ C .id , g ⟫) ⋆⟨ E ⟩ (F ⟪ f , D .id ⟫)
  BinMorphDecompR (f , g) F =
    (F ⟪ f , g ⟫)
      ≡⟨ (λ i → F ⟪ C .⋆IdL f (~ i), D .⋆IdR g (~ i)⟫) ⟩
    (F ⟪ C .id ⋆⟨ C ⟩ f , g ⋆⟨ D ⟩ D .id ⟫)
      ≡⟨ F .F-seq (C .id , g) (f , D .id) ⟩
    (F ⟪ C .id , g ⟫) ⋆⟨ E ⟩ (F ⟪ f , D .id ⟫) ∎

  open NatIso
  open NatTrans

  -- Natural isomorphism in each component yields naturality of bifunctor
  binaryNatIso : ∀ (F G : Functor (C ×C D) E)
    → ( βc : (∀ (c : C .ob) →
           NatIso (((curryF D E {Γ = C}) ⟅ F ⟆) ⟅ c ⟆)
                  (((curryF D E {Γ = C}) ⟅ G ⟆) ⟅ c ⟆)))
    → ( βd : (∀ (d : D .ob) →
           NatIso (((curryFl C E {Γ = D}) ⟅ F ⟆) ⟅ d ⟆)
                  (((curryFl C E {Γ = D}) ⟅ G ⟆) ⟅ d ⟆)))
    → ( ∀ ((c , d) : (C ×C D) .ob) →
        ((βc c .trans .N-ob d) ≡ (βd d .trans .N-ob c)))
    → NatIso F G
  binaryNatIso F G βc βd β≡ .trans .N-ob (c , d) = (βc c) .trans .N-ob d
  binaryNatIso F G βc βd β≡ .trans .N-hom {(c₁ , d₁)} {(c₂ , d₂)} (fc , fd) =
    ((F ⟪ fc , fd ⟫) ⋆⟨ E ⟩ ((βc c₂) .trans .N-ob d₂))
      ≡⟨ (λ i →
        ((BinMorphDecompL (fc , fd) F) (i)) ⋆⟨ E ⟩ ((βc c₂) .trans .N-ob d₂)) ⟩
    (((F ⟪ fc , D .id ⟫) ⋆⟨ E ⟩
      (F ⟪ C .id , fd ⟫)) ⋆⟨ E ⟩ ((βc c₂) .trans .N-ob d₂))
      ≡⟨ solveCat! E ⟩
    ((F ⟪ fc , D .id ⟫) ⋆⟨ E ⟩
      ((F ⟪ C .id , fd ⟫) ⋆⟨ E ⟩ ((βc c₂) .trans .N-ob d₂)))
      ≡⟨ (λ i → (F ⟪ fc , D .id ⟫) ⋆⟨ E ⟩ ((βc c₂) .trans .N-hom fd (i))) ⟩
    ((F ⟪ fc , D .id ⟫) ⋆⟨ E ⟩
      (((βc c₂) .trans .N-ob d₁) ⋆⟨ E ⟩ (G ⟪ C .id , fd ⟫)))
      ≡⟨ (λ i → (F ⟪ fc , D .id ⟫) ⋆⟨ E ⟩
        (((β≡ (c₂ , d₁)) (i)) ⋆⟨ E ⟩ (G ⟪ C .id , fd ⟫))) ⟩
    ((F ⟪ fc , D .id ⟫) ⋆⟨ E ⟩
      (((βd d₁) .trans .N-ob c₂) ⋆⟨ E ⟩ (G ⟪ C .id , fd ⟫)))
      ≡⟨ solveCat! E ⟩
    (((F ⟪ fc , D .id ⟫) ⋆⟨ E ⟩
      ((βd d₁) .trans .N-ob c₂)) ⋆⟨ E ⟩ (G ⟪ C .id , fd ⟫))
      ≡⟨ (λ i → ((βd  d₁) .trans .N-hom fc (i)) ⋆⟨ E ⟩ (G ⟪ C .id , fd ⟫)) ⟩
    ((((βd d₁) .trans .N-ob c₁) ⋆⟨ E ⟩
      (G ⟪ fc , D .id ⟫)) ⋆⟨ E ⟩ (G ⟪ C .id , fd ⟫))
      ≡⟨ solveCat! E ⟩
    (((βd d₁) .trans .N-ob c₁) ⋆⟨ E ⟩
      ((G ⟪ fc , D .id ⟫) ⋆⟨ E ⟩ (G ⟪ C .id , fd ⟫)))
      ≡⟨ (λ i → ((βd d₁) .trans .N-ob c₁) ⋆⟨ E ⟩
        ((BinMorphDecompL (fc , fd) G) (~ i))) ⟩
    (((βd  d₁) .trans .N-ob c₁) ⋆⟨ E ⟩ (G ⟪ fc , fd ⟫))
      ≡⟨ (λ i → (β≡ (c₁ , d₁) (~ i)) ⋆⟨ E ⟩ (G ⟪ fc , fd ⟫)) ⟩
    (((βc c₁) .trans .N-ob d₁) ⋆⟨ E ⟩ (G ⟪ fc , fd ⟫)) ∎
  binaryNatIso F G βc βd β≡ .nIso (c , d)  = (βc c) .nIso d

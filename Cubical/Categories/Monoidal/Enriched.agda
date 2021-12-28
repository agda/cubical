-- Enriched categories
{-# OPTIONS --safe #-}

module Cubical.Categories.Monoidal.Enriched where

open import Cubical.Categories.Monoidal.Base
open import Cubical.Foundations.Prelude

module _ {ℓV ℓV' : Level} (V : MonoidalCategory ℓV ℓV') (ℓE : Level) where

  open MonoidalCategory V
    renaming (ob to obV; Hom[_,_] to V[_,_]; id to idV; _⋆_ to _⋆V_)

  record EnrichedCategory : Type (ℓ-max (ℓ-max ℓV ℓV') (ℓ-suc ℓE)) where
    field
      ob : Type ℓE
      Hom[_,_] : ob → ob → obV
      id : ∀ {x} → V[ unit , Hom[ x , x ] ]
      seq : ∀ x y z → V[ Hom[ x , y ] ⊗ Hom[ y , z ] , Hom[ x , z ] ]

      -- Axioms
      ⋆IdL : ∀ x y →   η⟨ _ ⟩  ≡  (id {x} ⊗ₕ idV)  ⋆V  (seq x x y)
      ⋆IdR : ∀ x y →   ρ⟨ _ ⟩  ≡  (idV ⊗ₕ id {y})  ⋆V  (seq x y y)
      ⋆Assoc : ∀ x y z w →
          α⟨ _ , _ , _ ⟩  ⋆V  ((seq x y z) ⊗ₕ idV)  ⋆V  (seq x z w)
                          ≡  (idV ⊗ₕ (seq y z w))  ⋆V  (seq x y w)


-- TODO: define underlying category using Hom[ x , y ] := V[ unit , Hom[ x , y ] ]

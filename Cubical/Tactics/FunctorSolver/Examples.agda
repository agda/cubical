
{-
   The functor solver solveFunctor! C D F solves equations in a
   category D that hold up to associativity/unit in D as well as
   Functoriality of the functor F.

   This file shows some examples of how to use it.
-}

module Cubical.Tactics.FunctorSolver.Examples where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Tactics.FunctorSolver.Reflection

private
  variable
    ℓ ℓ' : Level
    C D : Category ℓ ℓ'
    F : Functor C D

module Examples (F : Functor C D) where
  open Category
  open Functor

  _ : ∀ {A B}{f : D [ A , B ]}
    → D .id ∘⟨ D ⟩ f ≡ f ∘⟨ D ⟩ D .id
  _ = solveFunctor! C D F

  _ : ∀ {A}
    → D .id ≡ F ⟪ (C .id {A}) ⟫
  _ = solveFunctor! C D F


  _ : {W X Y : C .ob}
      → {Z : D .ob}
      → {f : C [ W , X ]}
      → {g : C [ X , Y ]}
      → {h : D [ F ⟅ Y ⟆ , Z ]}
      → h ∘⟨ D ⟩ F ⟪ (g ∘⟨ C ⟩ C .id) ∘⟨ C ⟩ f ⟫ ∘⟨ D ⟩ F ⟪ C .id ⟫
        ≡ D .id ∘⟨ D ⟩ h ∘⟨ D ⟩ F ⟪ C .id ∘⟨ C ⟩ g ⟫ ∘⟨ D ⟩ F ⟪ f ⟫
  _ = solveFunctor! C D F

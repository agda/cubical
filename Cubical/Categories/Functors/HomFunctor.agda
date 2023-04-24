{-# OPTIONS --safe #-}

module Cubical.Categories.Functors.HomFunctor where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Constructions.BinProduct

private
  variable
    ℓC ℓC' : Level

module _ (C : Category ℓC ℓC') where

  open Functor
  open Category C

  HomFunctor : Functor (C ^op ×C C) (SET ℓC')
  F-ob HomFunctor (x , y) = Hom[ x , y ] , isSetHom
  F-hom HomFunctor {x , y} {x' , y'} (φ , ψ) θ = ψ ∘ (θ ∘ φ)
  F-id HomFunctor = funExt λ θ → ⋆IdR (id ⋆ θ) ∙ ⋆IdL θ
  F-seq HomFunctor {x , y} {x' , y'} {x'' , y''} (φ , ψ) (φ' , ψ') = funExt λ θ →
    ((φ' ⋆ φ) ⋆ θ) ⋆ (ψ ⋆ ψ')
      ≡⟨ sym (⋆Assoc ((φ' ⋆ φ) ⋆ θ) ψ ψ') ⟩
    (((φ' ⋆ φ) ⋆ θ) ⋆ ψ) ⋆ ψ'
      ≡⟨ cong (_⋆ ψ') (
        ((φ' ⋆ φ) ⋆ θ) ⋆ ψ
          ≡⟨ cong (_⋆ ψ) (⋆Assoc φ' φ θ) ⟩
        (φ' ⋆ (φ ⋆ θ)) ⋆ ψ
          ≡⟨ ⋆Assoc φ' (φ ⋆ θ) ψ ⟩
        φ' ⋆ ((φ ⋆ θ) ⋆ ψ) ∎
      ) ⟩
    (φ' ⋆ ((φ ⋆ θ) ⋆ ψ)) ⋆ ψ' ∎

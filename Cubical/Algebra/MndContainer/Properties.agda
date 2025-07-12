{-# OPTIONS --safe #-}

module Cubical.Algebra.MndContainer.Properties where

open import Cubical.Foundations.Prelude hiding (_▷_) renaming (fst to π₁ ; snd to π₂)
open import Cubical.Foundations.Function
open import Cubical.Algebra.MndContainer.Base
open import Cubical.Data.Sigma
open import Cubical.Data.Containers.Set.Base
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Categories.Functor
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Monad.Base
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.NaturalTransformation.Properties
open import Cubical.Categories.Instances.Sets

private
  variable
    ℓs ℓp : Level

module _ (C : SetCon {ℓs} {ℓp}) (isMnd : IsMonad ⟦ C ⟧f) where
  open MndContainer
  open IsMndContainer
  open IsMonad isMnd

  fromMonad : MndContainer {ℓs} {ℓp} C
  ι fromMonad = {!   !}
  σ fromMonad = {!   !}
  pr₁ fromMonad = {!   !}
  pr₂ fromMonad = {!   !}
  unit-l (isMndContainer fromMonad) = {!   !}
  unit-r (isMndContainer fromMonad) = {!   !}
  assoc (isMndContainer fromMonad) = {!   !}
  pr-unit-r (isMndContainer fromMonad) = {!   !}
  pr-unit-l (isMndContainer fromMonad) = {!   !}
  pr-mul₁ (isMndContainer fromMonad) = {!   !}
  pr-mul₁₂ (isMndContainer fromMonad) = {!   !}
  pr-mul₂₂ (isMndContainer fromMonad) = {!   !}

module _ (C : SetCon {ℓs} {ℓp}) (mCont : MndContainer {ℓs} {ℓp} C) where
  open MndContainer mCont
  open IsMndContainer isMndContainer
  open NatTrans
  open IsMonad

  toMonad : IsMonad ⟦ C ⟧f
  N-ob (η toMonad) X x = (ι , const x)
  N-hom (η toMonad) f = refl
  N-ob (μ toMonad) X (s , f) = (σ s (fst ∘ f) , λ p → snd (f (pr₁ _ _ p)) (pr₂ _ _ p))
  N-hom (μ toMonad) f = refl
  idl-μ toMonad = natEqSET {ℓ-max ℓs ℓp} F-rUnit
    (compTrans (μ toMonad) (η toMonad ∘ˡ ⟦ C ⟧f))
    (idTrans ⟦ C ⟧f)
    (λ X i x → (unit-l (fst x) i , λ p → snd x (pr-unit-l i p)))
  idr-μ toMonad = natEqSET {ℓ-max ℓs ℓp} F-lUnit
    (compTrans (μ toMonad) (⟦ C ⟧f ∘ʳ η toMonad))
    (idTrans ⟦ C ⟧f)
    (λ X i x → (unit-r (fst x) i , λ p → snd x (pr-unit-r i p)))
  assoc-μ toMonad = natEqSET {ℓ-max ℓs ℓp} F-assoc
    (compTrans (μ toMonad) (⟦ C ⟧f ∘ʳ μ toMonad))
    (compTrans (μ toMonad) (μ toMonad ∘ˡ ⟦ C ⟧f))
    (λ X i x → (assoc (fst x) (fst ∘ (snd x)) (λ p p' → fst (snd (snd x p) p')) i 
                , λ p → snd (snd (snd x (pr-mul₁ i p)) (pr-mul₁₂ i p)) (pr-mul₂₂ i p)
                )
    )

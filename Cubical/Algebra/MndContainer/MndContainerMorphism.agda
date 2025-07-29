{-# OPTIONS --safe #-}

module Cubical.Algebra.MndContainer.MndContainerMorphism where

open import Cubical.Foundations.Prelude hiding (_▷_) renaming (fst to π₁ ; snd to π₂)
open import Cubical.Foundations.Function
open import Cubical.Algebra.MndContainer.Base
open import Cubical.Data.Sigma
open import Cubical.Data.Containers.Set.Base

private
  variable
    ℓs ℓp ℓs' ℓp' : Level

open SetCon
open MndContainer

record IsMndContainerMorphism (S : Type ℓs) (P : S → Type ℓp) (setS : isSet S) (setP : ∀ {s} → isSet (P s))
                              (T : Type ℓs') (Q : T → Type ℓp') (setT : isSet T) (setQ : ∀ {t} → isSet (Q t))
                              (Aₘ : MndContainer (S ◁ P & setS & setP)) 
                              (Bₘ : MndContainer (T ◁ Q & setT & setQ))
                              (shapeₘ : S → T) (positionₘ : {s : S} → Q (shapeₘ s) → P s) : 
                              Type (ℓ-suc (ℓ-max ℓs (ℓ-max ℓs' (ℓ-max ℓp ℓp')))) where
  field
    ι-pres : shapeₘ (ι Aₘ) ≡ ι Bₘ
    σ-pres : (s : S) (f : P s → S) → shapeₘ (σ Aₘ s f) ≡ σ Bₘ (shapeₘ s) (shapeₘ ∘ f ∘ positionₘ)
    pr₁-pres : (s : S) (f : P s → S) →
               PathP (λ i → Q (σ-pres s f i) → P s)
                     (λ q → pr₁ Aₘ s f (positionₘ q))
                     (λ q → positionₘ (pr₁ Bₘ (shapeₘ s) (shapeₘ ∘ f ∘ positionₘ) q))
    pr₂-pres : (s : S) (f : P s → S) →
               PathP (λ i → (q : Q (σ-pres s f i)) → P (f (pr₁-pres s f i q)))
                     (λ q → pr₂ Aₘ s f (positionₘ q))
                     (λ q → positionₘ (pr₂ Bₘ (shapeₘ s) (shapeₘ ∘ f ∘ positionₘ) q))


record MndContainerMorphism (S : Type ℓs) (P : S → Type ℓp) (setS : isSet S) (setP : ∀ {s} → isSet (P s))
                            (T : Type ℓs') (Q : T → Type ℓp') (setT : isSet T) (setQ : ∀ {t} → isSet (Q t))
                            (Aₘ : MndContainer (S ◁ P & setS & setP)) 
                            (Bₘ : MndContainer (T ◁ Q & setT & setQ)) :
                            Type (ℓ-suc (ℓ-max ℓs (ℓ-max ℓs' (ℓ-max ℓp ℓp')))) where
  field
    shapeₘ : S → T
    positionₘ : {s : S} → Q (shapeₘ s) → P s 
    isMCMorphism : IsMndContainerMorphism S P setS setP T Q setT setQ Aₘ Bₘ shapeₘ positionₘ


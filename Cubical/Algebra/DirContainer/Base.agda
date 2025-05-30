{-# OPTIONS --safe #-}

module Cubical.Algebra.DirContainer.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Containers.Set.Base

private
  variable
    ℓs ℓp : Level

open SetCon

record DirectedContainer (C : SetCon {ℓs} {ℓp}) : Type (ℓ-suc (ℓ-max ℓs ℓp)) where
  S = Shape C
  P = Position C
  field
    o : (s : S) → P s
    _↓_ : (s : S) → P s → S
    _⊕_ : {s : S} → (p : P s) → P (s ↓ p) → P s 
    unitl-↓ : (s : S) → s ↓ (o _) ≡ s
    distr-↓-⊕ : (s : S) (p : P s) (p' : P (s ↓ p)) →
                s ↓ (p ⊕ p') ≡ (s ↓ p) ↓ p'
    unitl-⊕ : (s : S) (p : P (s ↓ o s)) → 
              PathP (λ i → P (unitl-↓ s (~ i))) (o s ⊕ p) p
    unitr-⊕ : (s : S) (p : P s) → p ⊕ (o (s ↓ p)) ≡ p
    assoc-⊕ : (s : S) (p : P s) (p' : P (s ↓ p)) →
              PathP (λ i → P (distr-↓-⊕ s p p' i) → P s)
                    (λ p'' → (p ⊕ p') ⊕ p'')
                    (λ p'' → p ⊕ (p' ⊕ p''))

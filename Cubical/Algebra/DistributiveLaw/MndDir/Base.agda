{-# OPTIONS --safe #-}

module Cubical.Algebra.DistributiveLaw.MndDir.Base where

open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.DirContainer as DC
open import Cubical.Algebra.MndContainer as MC
open import Cubical.Algebra.DistributiveLaw.Base
open import Cubical.Data.Containers.Set.Base

open DC.DirContainer
open MC.MndContainer

private
  variable
    ℓs ℓp : Level
    
-- Distributive law direction: Aₘ ∘ Bₘ → Bₘ ∘ Aₘ
record MndDirDistributiveLaw (S : Type ℓs) (P : S → Type ℓp) (setS : isSet S) (setP : ∀ {s} → isSet (P s))
                             (T : Type ℓs) (Q : T → Type ℓp) (setT : isSet T) (setQ : ∀ {t} → isSet (Q t))
                             (Aₘ : DirContainer (S ◁ P & setS & setP)) (Bₘ : MndContainer (T ◁ Q & setT & setQ)) :
                             Type (ℓ-suc (ℓ-max ℓs ℓp)) where

  _⊕ᵃ_ = _⊕_ Aₘ
  _↓ᵃ_ = _↓_ Aₘ
  
  field
    u₁ : (s : S) (f : P s → T) → T
    u₂ : (s : S) (f : P s → T) → Q (u₁ s f) → S

    v₁ : {s : S} {f : P s → T} (q : Q (u₁ s f)) → P (u₂ s f q) → P s
    v₂ : {s : S} {f : P s → T} (q : Q (u₁ s f)) (p : P (u₂ s f q)) → Q (f (v₁ q p))

    unit-oA-shape : (s : S) (f : P s → T) → u₁ s f ≡ f (o Aₘ s)
    unit-oA-pos₁ : (s : S) (f : P s → T) → 
                   PathP (λ i → (q : Q (unit-oA-shape s f i)) → P s) 
                         (λ q → v₁ q (o Aₘ (u₂ s f q))) 
                         (λ q → o Aₘ s)
    unit-oA-pos₂ : (s : S) (f : P s → T) →
                   PathP (λ i → (q : Q (unit-oA-shape s f i)) → Q (f (unit-oA-pos₁ s f i q)))
                         (λ q → v₂ q (o Aₘ (u₂ s f q)))
                         (λ q → q)

    -- Redundant - follows from unit-oA-shape
    mul-A-shape₁ : (s : S) (f : P s → T) → u₁ s f ≡ u₁ s (λ p → u₁ (s ↓ᵃ p) (λ p' → f (p ⊕ᵃ p')))
    -- Redundant - follows from unit-oA-shape
    mul-A-shape₂ : (s : S) (f : P s → T) → 
                   PathP (λ i → (q : Q (mul-A-shape₁ s f i)) → S) 
                         (λ q → u₂ s f q)
                         (λ q → u₂ s (λ p → u₁ (s ↓ᵃ p) (λ p' → f (p ⊕ᵃ p'))) q)
    mul-A-shape₃ : (s : S) (f : P s → T) → 
                   PathP (λ i → (q : Q (mul-A-shape₁ s f i)) (p : P (mul-A-shape₂ s f i q)) → S)
                         (λ q p → u₂ s f q ↓ᵃ p) 
                         (λ q p → u₂ (s ↓ᵃ v₁ q p) (λ p' → f (v₁ q p ⊕ᵃ p')) (v₂ q p))

    mul-A-pos₁ : (s : S) (f : P s → T) →
                 PathP (λ i → (q : Q (mul-A-shape₁ s f i)) (p : P (mul-A-shape₂ s f i q)) → P (mul-A-shape₃ s f i q p) → P s)
                       (λ q p p' → v₁ q (p ⊕ᵃ p'))
                       (λ q p p' → v₁ q p ⊕ᵃ v₁ (v₂ q p) p')
    mul-A-pos₂ : (s : S) (f : P s → T) →
                 PathP (λ i → (q : Q (mul-A-shape₁ s f i)) (p : P (mul-A-shape₂ s f i q)) → (p' : P (mul-A-shape₃ s f i q p)) → Q (f (mul-A-pos₁ s f i q p p')))
                       (λ q p p' → v₂ q (p ⊕ᵃ p'))
                       (λ q p p' → v₂ (v₂ q p) p')

    -- Redundant - follows from unit-oA-shape
    unit-ιB-shape₁ : (s : S) → u₁ s (const (ι Bₘ)) ≡ ι Bₘ
    unit-ιB-shape₂ : (s : S) → 
                     PathP (λ i → (q : Q (unit-ιB-shape₁ s i)) → S)
                           (u₂ s (const (ι Bₘ)))
                           (const s)

    unit-ιB-pos₁ : (s : S) →
                   PathP (λ i → (q : Q (unit-ιB-shape₁ s i)) → P (unit-ιB-shape₂ s i q) → P s)
                         v₁
                         (λ q p → p)
    
    unit-ιB-pos₂ : (s : S) →
                   PathP (λ i → (q : Q (unit-ιB-shape₁ s i)) → (p : P (unit-ιB-shape₂ s i q)) → Q (ι Bₘ))
                         v₂
                         (λ q p → q)

    -- Redundant - follows from unit-oA-shape
    mul-B-shape₁ : (s : S) (f : P s → T) (g : (p : P s) → Q (f p) → T) →
                   u₁ s (uncurry (σ Bₘ) ∘ [ P , _ , _ ]⟨ f , g ⟩') 
                    ≡ σ Bₘ (u₁ s f) (uncurry u₁ ∘ [ Q , _ , _ ]⟨ u₂ s f , (λ q p → g (v₁ q p) (v₂ q p)) ⟩')

    mul-B-shape₂ : (s : S) (f : P s → T) (g : (p : P s) → Q (f p) → T) →
                   PathP (λ i → Q (mul-B-shape₁ s f g i) → S)
                         (λ q → u₂ s (uncurry (σ Bₘ) ∘ [ P , _ , _ ]⟨ f , g ⟩') q )
                         (λ q → (uncurry (uncurry u₂ ∘ [ Q , _ , _ ]⟨ u₂ s f , (λ q p → g (v₁ q p) (v₂ q p)) ⟩') ∘ pr Bₘ _ _) q)

    mul-B-pos₁ : (s : S) (f : P s → T) (g : (p : P s) → Q (f p) → T) →
                 PathP (λ i → (q : Q (mul-B-shape₁ s f g i)) (p : P (mul-B-shape₂ s f g i q)) → P s)
                       (λ q p → v₁ q p)
                       (λ q p → v₁ (pr₁ Bₘ _ _ q) (v₁ (pr₂ Bₘ _ _ q) p))

    mul-B-pos₂₁ : (s : S) (f : P s → T) (g : (p : P s) → Q (f p) → T) →
                  PathP (λ i → (q : Q (mul-B-shape₁ s f g i)) (p : P (mul-B-shape₂ s f g i q)) → Q (f (mul-B-pos₁ s f g i q p)))
                        (λ q p → pr₁ Bₘ _ _ (v₂ q p)) 
                        (λ q p → v₂ (pr₁ Bₘ _ _ q) (v₁ (pr₂ Bₘ _ _ q) p))
                 
    mul-B-pos₂₂ : (s : S) (f : P s → T) (g : (p : P s) → Q (f p) → T) →
                  PathP (λ i → (q : Q (mul-B-shape₁ s f g i)) (p : P (mul-B-shape₂ s f g i q)) →
                               Q (g (mul-B-pos₁ s f g i q p) (mul-B-pos₂₁ s f g i q p))) 
                        (λ q p → pr₂ Bₘ _ _ (v₂ q p))
                        (λ q p → v₂ (pr₂ Bₘ _ _ q) p)

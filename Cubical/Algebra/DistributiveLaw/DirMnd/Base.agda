{-# OPTIONS --safe #-}

module Cubical.Algebra.DistributiveLaw.DirMnd.Base where

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
record DirMndDistributiveLaw (S : Type ℓs) (P : S → Type ℓp) (setS : isSet S) (setP : ∀ {s} → isSet (P s))
                             (T : Type ℓs) (Q : T → Type ℓp) (setT : isSet T) (setQ : ∀ {t} → isSet (Q t))
                             (Aₘ : MndContainer (S ◁ P & setS & setP)) (Bₘ : DirContainer (T ◁ Q & setT & setQ)) :
                             Type (ℓ-suc (ℓ-max ℓs ℓp)) where

  _⊕ᵇ_ = _⊕_ Bₘ
  _↓ᵇ_ = _↓_ Bₘ
  
  field
    u₁ : (s : S) (f : P s → T) → T
    u₂ : (s : S) (f : P s → T) → Q (u₁ s f) → S

    v₁ : {s : S} {f : P s → T} (q : Q (u₁ s f)) → P (u₂ s f q) → P s
    v₂ : {s : S} {f : P s → T} (q : Q (u₁ s f)) (p : P (u₂ s f q)) → Q (f (v₁ q p))

    unit-ιA-shape₁ : (t : T) → u₁ (ι Aₘ) (const t) ≡ t
    unit-ιA-shape₂ : (t : T) → 
                     PathP (λ i → (q : Q (unit-ιA-shape₁ t i)) → S)
                           (u₂ (ι Aₘ) (const t)) 
                           (const (ι Aₘ))

    unit-ιA-pos₁ : (t : T) →
                   PathP (λ i → (q : Q (unit-ιA-shape₁ t i)) → P (unit-ιA-shape₂ t i q) → P (ι Aₘ))
                         v₁
                         (λ q p → p)
                   
    unit-ιA-pos₂ : (t : T) →
                   PathP (λ i → (q : Q (unit-ιA-shape₁ t i)) → P (unit-ιA-shape₂ t i q) → Q t)
                         v₂
                         (λ q p → q)

    mul-A-shape₁ : (s : S) (f : P s → S) (g : (p : P s) → P (f p) → T) →
                   u₁ (σ Aₘ s f) (uncurry g ∘ (pr Aₘ _ _)) ≡
                   u₁ s (uncurry u₁ ∘ [ P , _ , _ ]⟨ f , g ⟩')
    
    mul-A-shape₂ : (s : S) (f : P s → S) (g : (p : P s) → P (f p) → T) →
                   PathP (λ i → Q (mul-A-shape₁ s f g i) → S)
                         (λ q → (u₂ (σ Aₘ s f) (uncurry g ∘ pr Aₘ _ _)) q)
                         (λ q → uncurry (σ Aₘ) ([ Q , P , _ ]⟨ u₂ s (uncurry u₁ ∘ [ P , _ , _ ]⟨ f , g ⟩') ,
                                                               (λ q p → (uncurry u₂ ∘ [ P , _ , _ ]⟨ f , g ⟩') (v₁ q p) (v₂ q p)) ⟩' q))

    mul-A-pos₁ : (s : S) (f : P s → S) (g : (p : P s) → P (f p) → T) →
                 PathP (λ i → (q : Q (mul-A-shape₁ s f g i)) → P (mul-A-shape₂ s f g i q) → P s)
                       (λ q p → pr₁ Aₘ s _ (v₁ q p))
                       (λ q p → v₁ q (pr₁ Aₘ _ _ p))

    mul-A-pos₂₁ : (s : S) (f : P s → S) (g : (p : P s) → P (f p) → T) →
                  PathP (λ i → (q : Q (mul-A-shape₁ s f g i)) (p : P (mul-A-shape₂ s f g i q)) → P (f (mul-A-pos₁ s f g i q p)))
                        (λ q p → pr₂ Aₘ _ _ (v₁ q p))
                        (λ q p → v₁ (v₂ q (pr₁ Aₘ _ _ p)) (pr₂ Aₘ _ _ p))     

    mul-A-pos₂₂ : (s : S) (f : P s → S) (g : (p : P s) → P (f p) → T) →
                  PathP (λ i → (q : Q (mul-A-shape₁ s f g i)) (p : P (mul-A-shape₂ s f g i q)) → Q (g (mul-A-pos₁ s f g i q p) (mul-A-pos₂₁ s f g i q p)))
                        (λ q p → v₂ q p) 
                        (λ q p → v₂ (v₂ q (pr₁ Aₘ _ _ p)) (pr₂ Aₘ _ _ p))  

    unit-oB-shape : (s : S) (f : P s → T) → u₂ s f (o Bₘ _) ≡ s
    unit-oB-pos₁ : (s : S) (f : P s → T) (p : P (u₂ s f (o Bₘ _))) → 
                   PathP (λ i → P (unit-oB-shape s f (~ i))) 
                   (v₁ (o Bₘ _) p)
                   p
    unit-oB-pos₂ : (s : S) (f : P s → T) (p : P (u₂ s f (o Bₘ _))) → v₂ (o Bₘ _) p ≡ o Bₘ _

    mul-B-shape₁ : (s : S) (f : P s → T) (q : Q (u₁ s f)) → u₁ s f ↓ᵇ q ≡ u₁ (u₂ s f q) (λ p → f (v₁ q p) ↓ᵇ v₂ q p)

    mul-B-shape₂ : (s : S) (f : P s → T) (q : Q (u₁ s f)) → 
                   PathP (λ i → (q' : Q (mul-B-shape₁ s f q i)) → S)
                         (λ q' → u₂ s f (q ⊕ᵇ q'))
                         (λ q' → u₂ (u₂ s f q) (λ p → f (v₁ q p) ↓ᵇ v₂ q p) q')

    mul-B-pos₁ : (s : S) (f : P s → T) (q : Q (u₁ s f)) →
                 PathP (λ i → (q' : Q (mul-B-shape₁ s f q i)) (p : P (mul-B-shape₂ s f q i q')) → P s) 
                       (λ q' p → v₁ (q ⊕ᵇ q') p)
                       (λ q' p → v₁ q (v₁ q' p))
    mul-B-pos₂ : (s : S) (f : P s → T) (q : Q (u₁ s f)) → 
                 PathP (λ i → (q' : Q (mul-B-shape₁ s f q i)) (p : P (mul-B-shape₂ s f q i q')) → Q (f (mul-B-pos₁ s f q i q' p))) 
                       (λ q' p → v₂ (q ⊕ᵇ q') p) 
                       (λ q' p → v₂ q (v₁ q' p) ⊕ᵇ (v₂ q' p))

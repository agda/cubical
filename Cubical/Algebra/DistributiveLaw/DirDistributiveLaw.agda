{-# OPTIONS --safe #-}

module Cubical.Algebra.DistributiveLaw.DirDistributiveLaw where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.DirContainer as DC
open import Cubical.Algebra.DistributiveLaw.Base
open import Cubical.Data.Containers.Set.Base

open DC.DirContainer

private
  variable
    ℓs ℓp : Level

-- Distributive law direction: Aₘ ∘ Bₘ → Bₘ ∘ Aₘ
record DirectedDistributiveLaw (S : Type ℓs) (P : S → Type ℓp) (setS : isSet S) (setP : ∀ {s} → isSet (P s))
                               (T : Type ℓs) (Q : T → Type ℓp) (setT : isSet T) (setQ : ∀ {t} → isSet (Q t))
                               (Aₘ : DirContainer (S ◁ P & setS & setP)) (Bₘ : DirContainer (T ◁ Q & setT & setQ)) :
                               Type (ℓ-suc (ℓ-max ℓs ℓp)) where
  
  _⊕ᵃ_ = _⊕_ Aₘ
  _↓ᵃ_ = _↓_ Aₘ
  _⊕ᵇ_ = _⊕_ Bₘ
  _↓ᵇ_ = _↓_ Bₘ
  
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

    mul-A-shape₁ : (s : S) (f : P s → T) → u₁ s f ≡ u₁ s (λ p → u₁ (s ↓ᵃ p) (λ p' → f (p ⊕ᵃ p')))
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
                         (λ q' → u₂ (u₂ s f q) ((λ p → f (v₁ q p) ↓ᵇ v₂ q p)) q')

    mul-B-pos₁ : (s : S) (f : P s → T) (q : Q (u₁ s f)) →
                 PathP (λ i → (q' : Q (mul-B-shape₁ s f q i)) (p : P (mul-B-shape₂ s f q i q')) → P s) 
                       (λ q' p → v₁ (q ⊕ᵇ q') p)
                       (λ q' p → v₁ q (v₁ q' p))
    mul-B-pos₂ : (s : S) (f : P s → T) (q : Q (u₁ s f)) → 
                 PathP (λ i → (q' : Q (mul-B-shape₁ s f q i)) (p : P (mul-B-shape₂ s f q i q')) → Q (f (mul-B-pos₁ s f q i q' p))) 
                       (λ q' p → v₂ (q ⊕ᵇ q') p) 
                       (λ q' p → v₂ q (v₁ q' p) ⊕ᵇ (v₂ q' p))

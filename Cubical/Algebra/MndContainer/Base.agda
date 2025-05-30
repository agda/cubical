{-# OPTIONS --safe #-}

module Cubical.Algebra.MndContainer.Base where

open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
open import Cubical.Data.Containers.Set.Base

private
  variable
    ℓs ℓp : Level

record IsMndContainer (S : Type ℓs) (P : S → Type ℓp)
                      (ι : S) 
                      (σ : (s : S) → (P s → S) → S)
                      (pr₁ : (s : S) (f : P s → S) → P (σ s f) → P s)
                      (pr₂ : (s : S) (f : P s → S) (p : P (σ s f)) → P (f (pr₁ s f p))) : 
                      Type (ℓ-suc (ℓ-max ℓs ℓp)) where
  field
    unit-l : (s : S) → σ ι (const s) ≡ s
    unit-r : (s : S) → σ s (const ι) ≡ s
    assoc : (a : S) (b : P a → S) (c : (p : P a) → P (b p) → S) →
            σ a (λ p → σ (b p) (c p)) ≡ σ (σ a b) (λ p → c (pr₁ _ _ p) (pr₂ _ _ p))
    pr-unit-r : {s : S} → 
                PathP (λ i → (p : P (unit-r s i)) → P s)
                      (pr₁ _ _) 
                      (λ p → p)
    pr-unit-l : {s : S} → 
                PathP (λ i → (p : P (unit-l s i)) → P s) 
                      (pr₂ _ _) 
                      (λ p → p)
    pr-mul₁ : {a : S} {b : P a → S} {c : (p : P a) → P (b p) → S} →
              PathP (λ i → P (assoc a b c i) → P a)
                    (λ q → pr₁ a (λ p → σ (b p) (c p)) q)
                    (λ q → pr₁ a b (pr₁ (σ a b) ((λ r → c (pr₁ _ _ r) (pr₂ _ _ r))) q))
    pr-mul₁₂ : {a : S} {b : P a → S} {c : (p : P a) → P (b p) → S} →
                PathP (λ i → (p : P (assoc a b c i)) → P (b (pr-mul₁ i p)))
                      (λ q → pr₁ _ _ (pr₂ _ _ q))
                      (λ q → pr₂ _ _ (pr₁ _ _ q))
    pr-mul₂₂ : {a : S} {b : P a → S} {c : (p : P a) → P (b p) → S} →
                PathP (λ i → (q : P (assoc a b c i)) → P (c (pr-mul₁ i q) (pr-mul₁₂ i q)))
                      (λ q → pr₂ _ _ (pr₂ _ _ q))
                      (λ q → pr₂ _ _ q)

open SetCon

record MndContainer (C : SetCon {ℓs} {ℓp}) : Type (ℓ-suc (ℓ-max ℓs ℓp)) where
  S = Shape C
  P = Position C
  field
    ι : S
    σ : (s : S) → (P s → S) → S
    pr₁ : (s : S) (f : P s → S) → P (σ s f) → P s
    pr₂ : (s : S) (f : P s → S) (p : P (σ s f)) → P (f (pr₁ s f p))
    isMndContainer : IsMndContainer S P ι σ pr₁ pr₂

  pr : (s : S) (f : P s → S) → P (σ s f) → Σ[ p ∈ P s ] P (f p)
  pr s f p = pr₁ _ _ p , pr₂ _ _ p

open MndContainer

mContBuilder : (S : Type ℓs) (P : S → Type ℓp) (setS : isSet S) (setP : ∀ {s} → isSet (P s))
               (ι : S) 
               (σ : (s : S) → (P s → S) → S)
               (pr₁ : (s : S) (f : P s → S) → P (σ s f) → P s)
               (pr₂ : (s : S) (f : P s → S) (p : P (σ s f)) → P (f (pr₁ s f p)))
               (isMndCont : IsMndContainer S P ι σ pr₁ pr₂) →
               MndContainer (S ◁ P & setS & setP)
ι (mContBuilder S P setS setP ι σ pr₁ pr₂ isMndCont) = ι
σ (mContBuilder S P setS setP ι σ pr₁ pr₂ isMndCont) = σ
pr₁ (mContBuilder S P setS setP ι σ pr₁ pr₂ isMndCont) = pr₁
pr₂ (mContBuilder S P setS setP ι σ pr₁ pr₂ isMndCont) = pr₂
isMndContainer (mContBuilder S P setS setP ι σ pr₁ pr₂ isMndCont) = isMndCont   

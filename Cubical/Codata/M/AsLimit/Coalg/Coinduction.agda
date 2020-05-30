{-# OPTIONS --cubical --guardedness #-} --safe

module Cubical.Codata.M.AsLimit.Coalg.Coinduction where

open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Prod

open import Cubical.Foundations.Function using ( _∘_ )
open import Cubical.Foundations.Prelude

open import Cubical.Functions.Embedding

open import Cubical.Codata.M.AsLimit.helper
open import Cubical.Codata.M.AsLimit.Coalg.Base
open import Cubical.Codata.M.AsLimit.Coalg.Properties
open import Cubical.Codata.M.AsLimit.Container
open import Cubical.Codata.M.AsLimit.M

-------------------------------
-- Bisimilarity of Coalgebra --
-------------------------------

-- Strong bisimilarity
record bisimulation {ℓ} (S : Container ℓ) (C,γ : Coalg₀ S) (R : C,γ .fst → C,γ .fst → Type ℓ) : Type (ℓ-suc ℓ) where
  coinductive

  R⁻ = Σ[ a ∈ (C,γ .fst) ] Σ[ b ∈ (C,γ .fst) ] (R a b)

  π₁ : R⁻ → C,γ .fst
  π₁ = fst

  π₂ : R⁻ → C,γ .fst
  π₂ = fst ∘ snd

  field
    αᵣ : R⁻ → P₀ S R⁻
    rel₁ : (C,γ .snd) ∘ π₁ ≡ P₁ π₁ ∘ αᵣ
    rel₂ : (C,γ .snd) ∘ π₂ ≡ P₁ π₂ ∘ αᵣ

  R⁻-coalg : Coalg₀ S
  R⁻-coalg = R⁻ , αᵣ

  prod₁ : R⁻-coalg ⇒ C,γ
  prod₁ = π₁ , rel₁

  prod₂ : R⁻-coalg ⇒ C,γ
  prod₂ = π₂ , rel₂

open bisimulation public

final-property-prod : ∀ {ℓ} (S : Container ℓ) R → (sim : bisimulation S M-coalg R) → prod₁ sim ≡ prod₂  sim
final-property-prod S R sim = final-coalg-property-2 {S = S} (R⁻-coalg sim) (M-final-coalg {S = S}) (prod₁ sim) (prod₂ sim)

final-property-π : ∀ {ℓ} (S : Container ℓ) R → (sim : bisimulation S M-coalg R) → π₁ sim ≡ π₂  sim
final-property-π S R sim = cong fst (final-property-prod S R sim)

-------------------------------------------------------------
-- Coinduction principle for M-types (≈ Coinductive types) --
-------------------------------------------------------------

-- coinduction proof by: m ≡ π₁(m,m',r) ≡ unfold-R ≡ π₂(m,m',r) ≡ m'
coinduction : ∀ {ℓ} {S : Container ℓ} R → (sim : bisimulation S M-coalg R) → ∀ {m m' : M S} → R m m' → m ≡ m'
coinduction {S = S} R sim {m} {m'} r = funExt⁻ (final-property-π S R sim) (m , (m' , r))

coinduction⁻ : ∀ {ℓ} {S : Container ℓ} R → (sim : bisimulation S M-coalg R) → (∀ {x} → R x x) →  ∀ {m m' : M S} → m ≡ m' → R m m'
coinduction⁻ {S = S} R sim k {m} {m'} r = subst (R m) r k

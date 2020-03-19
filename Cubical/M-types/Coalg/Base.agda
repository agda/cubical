{-# OPTIONS --cubical --guardedness #-} --safe

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using ( _∘_ )

open import Cubical.Data.Unit

open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
-- open import Cubical.Foundations.Id using (ap ; _∙_)
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Data.Nat
open import Cubical.Data.Prod
open import Cubical.M-types.helper

open import Cubical.Data.Sigma

module Cubical.M-types.Coalg.Base where

open import Cubical.M-types.Container

-------------------------------
-- Definition of a Coalgebra --
-------------------------------

Coalg₀ : ∀ {ℓ} {S : Container {ℓ}} -> Set (ℓ-suc ℓ)
Coalg₀ {ℓ} {S = S} = Σ (Set ℓ) λ C → C → P₀ {S = S} C

Coalg₁ : ∀ {ℓ} {S : Container {ℓ}} -> Coalg₀ {S = S} -> Coalg₀ {S = S} -> Set ℓ
Coalg₁ {S = S} (C , γ) (D , δ) = Σ (C → D) λ f → δ ∘ f ≡ (P₁ f) ∘ γ

-- Coalgebra morphism notation
_⇒_ = Coalg₁

--------------------------
-- Definition of a Cone --
--------------------------

Cone₀ : ∀ {ℓ} {S : Container {ℓ}} {C,γ : Coalg₀ {S = S}} -> Set ℓ
Cone₀ {S = S} {C , _} = (n : ℕ) → C → X (sequence S) n

Cone₁ : ∀ {ℓ} {S : Container {ℓ}} {C,γ : Coalg₀ {S = S}} -> (f : Cone₀ {C,γ = C,γ}) -> Set ℓ
Cone₁ {S = S} {C , _} f = (n : ℕ) → π (sequence S) ∘ (f (suc n)) ≡ f n

Cone : ∀ {ℓ} {S : Container {ℓ}} (C,γ : Coalg₀ {S = S}) -> Set ℓ
Cone {S = S} C,γ = Σ (Cone₀ {C,γ = C,γ}) (Cone₁{C,γ = C,γ})

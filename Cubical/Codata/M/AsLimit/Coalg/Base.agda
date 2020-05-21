{-# OPTIONS --cubical --guardedness --safe #-}

module Cubical.Codata.M.AsLimit.Coalg.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using ( _∘_ )
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Prod
open import Cubical.Data.Sigma

open import Cubical.Codata.M.AsLimit.Container
open import Cubical.Codata.M.AsLimit.helper

-------------------------------
-- Definition of a Coalgebra --
-------------------------------

Coalg₀ : ∀ {ℓ} {S : Container ℓ} -> Type (ℓ-suc ℓ)
Coalg₀ {ℓ} {S = S} = Σ[ C ∈ Type ℓ ] (C → P₀ S C)

--------------------------
-- Definition of a Cone --
--------------------------

Cone₀ : ∀ {ℓ} {S : Container ℓ} {C,γ : Coalg₀ {S = S}} -> Type ℓ
Cone₀ {S = S} {C , _} = (n : ℕ) → C → X (sequence S) n

Cone₁ : ∀ {ℓ} {S : Container ℓ} {C,γ : Coalg₀ {S = S}} -> (f : Cone₀ {C,γ = C,γ}) -> Type ℓ
Cone₁ {S = S} {C , _} f = (n : ℕ) → π (sequence S) ∘ (f (suc n)) ≡ f n

Cone : ∀ {ℓ} {S : Container ℓ} (C,γ : Coalg₀ {S = S}) -> Type ℓ
Cone {S = S} C,γ = Σ[ Cone ∈ (Cone₀ {C,γ = C,γ}) ] (Cone₁{C,γ = C,γ} Cone)

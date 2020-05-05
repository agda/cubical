{-# OPTIONS --cubical --guardedness --safe #-}

module Cubical.Codata.M-types.Container where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Foundations.Function using (_∘_)

open import Cubical.Data.Unit
open import Cubical.Data.Prod
open import Cubical.Data.Nat as ℕ using (ℕ ; suc ; _+_ )

open import Cubical.Foundations.Transport

open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function

open import Cubical.Data.Sum

open import Cubical.Foundations.Structure

open import Cubical.Codata.M-types.helper

-------------------------------------
-- Container and Container Functor --
-------------------------------------

-- Σ[ A ∈ (Type ℓ) ] (A → Type ℓ)
Container : ∀ ℓ -> Type (ℓ-suc ℓ)
Container ℓ = TypeWithStr ℓ (λ x → x → Type ℓ)

-- Polynomial functor (P₀ , P₁)  defined over a container
-- https://ncatlab.org/nlab/show/polynomial+functor

-- P₀ object part of functor
P₀ : ∀ {ℓ} (S : Container ℓ) -> Type ℓ -> Type ℓ
P₀ (A , B) X  = Σ[ a ∈ A ] (B a -> X)

-- P₁ morphism part of functor
P₁ : ∀ {ℓ} {S : Container ℓ} {X Y} (f : X -> Y) -> P₀ S X -> P₀ S Y
P₁ {S = S} f = λ { (a , g) ->  a , f ∘ g }

-----------------------
-- Chains and Limits --
-----------------------

record Chain ℓ : Type (ℓ-suc ℓ) where
  constructor _,,_
  field
    X : ℕ -> Type ℓ
    π : {n : ℕ} -> X (suc n) -> X n

open Chain public

limit-of-chain : ∀ {ℓ} -> Chain ℓ → Type ℓ
limit-of-chain (x ,, pi) = Σ[ x ∈ ((n : ℕ) → x n) ] ((n : ℕ) → pi {n = n} (x (suc n)) ≡ x n)

shift-chain : ∀ {ℓ} -> Chain ℓ -> Chain ℓ
shift-chain = λ X,π -> ((λ x → X X,π (suc x)) ,, λ {n} → π X,π {suc n})

------------------------------------------------------
-- Limit type of a Container , and Shift of a Limit --
------------------------------------------------------

W : ∀ {ℓ} -> Container ℓ -> ℕ -> Type ℓ
W S 0 = Lift Unit
W S (suc n) = P₀ S (W S n)

πₙ : ∀ {ℓ} -> (S : Container ℓ) -> {n : ℕ} -> W S (suc n) -> W S n
πₙ {ℓ} S {0} _ = lift tt
πₙ S {suc n} = P₁ (πₙ S {n})

sequence : ∀ {ℓ} -> Container ℓ -> Chain ℓ
X (sequence {ℓ} S) n = W {ℓ} S n
π (sequence {ℓ} S) {n} = πₙ {ℓ} S {n}

PX,Pπ : ∀ {ℓ} (S : Container ℓ) -> Chain ℓ
PX,Pπ {ℓ} S =
  (λ n → P₀ S (X (sequence S) n)) ,,
  (λ {n : ℕ} x → P₁ (λ z → z) (π (sequence S) {n = suc n} x ))

-----------------------------------
-- M-type is limit of a sequence --
-----------------------------------

M-type : ∀ {ℓ} -> Container ℓ → Type ℓ
M-type = limit-of-chain ∘ sequence

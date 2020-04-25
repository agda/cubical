{-# OPTIONS --cubical --guardedness #-} --safe

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

open import Cubical.Codata.M-types.helper

module Cubical.Codata.M-types.Container where

-------------------------------------
-- Container and Container Functor --
-------------------------------------

Container : ∀ {ℓ} -> Set (ℓ-suc ℓ)
Container {ℓ} = Σ (Set ℓ) (λ A -> A -> Set ℓ)

P₀ : ∀ {ℓ} {S : Container {ℓ}} -> Set ℓ -> Set ℓ
P₀ {S = S} X  = Σ (S .fst) λ x → (S .snd x) -> X

P₁ : ∀ {ℓ} {S : Container {ℓ}} {X Y} (f : X -> Y) -> P₀ {S = S} X -> P₀ {S = S} Y
P₁ {S = S} f = λ { (a , g) ->  a , f ∘ g }

-----------------------
-- Chains and Limits --
-----------------------

record Chain {ℓ} : Set (ℓ-suc ℓ) where
  constructor _,,_
  field
    X : ℕ -> Set ℓ
    π : {n : ℕ} -> X (suc n) -> X n

open Chain

L : ∀ {ℓ} -> Chain {ℓ} → Set ℓ
L (x ,, pi) = Σ ((n : ℕ) → x n) λ x → (n : ℕ) → pi {n = n} (x (suc n)) ≡ x n

shift-chain : ∀ {ℓ} -> Chain {ℓ} -> Chain {ℓ}
shift-chain = λ X,π -> ((λ x → X X,π (suc x)) ,, λ {n} → π X,π {suc n})

! : ∀ {ℓ} {A : Set ℓ} (x : A) -> Lift {ℓ-zero} {ℓ} Unit
! x = lift tt

------------------------------------------------------
-- Limit type of a Container , and Shift of a Limit --
------------------------------------------------------

W : ∀ {ℓ} -> Container {ℓ} -> ℕ -> Set ℓ -- (ℓ-max ℓ ℓ')
W S 0 = Lift Unit
W S (suc n) = P₀ {S = S} (W S n)

πₙ : ∀ {ℓ} -> (S : Container {ℓ}) -> {n : ℕ} -> W S (suc n) -> W S n
πₙ {ℓ} S {0} = ! {ℓ}
πₙ S {suc n} = P₁ (πₙ S {n})

sequence : ∀ {ℓ} -> Container {ℓ} -> Chain {ℓ}
X (sequence {ℓ} S) n = W {ℓ} S n
π (sequence {ℓ} S) {n} = πₙ {ℓ} S {n}

open Chain public

-----------------------------------
-- M-type is limit of a sequence --
-----------------------------------

M-type : ∀ {ℓ} -> Container {ℓ} → Set ℓ
M-type = L ∘ sequence

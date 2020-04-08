{-# OPTIONS --cubical --guardedness #-} --safe

open import Cubical.M-types.itree
open import Cubical.M-types.M-type
open import Cubical.M-types.Coalg

open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Sum
open import Cubical.Data.Empty
open import Cubical.Data.Bool

open import Cubical.Codata.Stream

open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence

open import Cubical.HITs.SetQuotients

open import Cubical.M-types.Container

module Cubical.M-types.bisim-examples where

-------------------------------
-- The identity bisimulation --
-------------------------------

Δ : ∀ {ℓ} {S : Container {ℓ}} -> bisimulation S M-coalg (_≡_)
αᵣ (Δ {S = S}) = λ a → fst (M-coalg .snd (a .fst)) , (λ b → snd (M-coalg .snd (a .fst)) b , (snd (M-coalg .snd (a .fst)) b , refl))
rel₁ (Δ {S = S}) = funExt λ x → refl
rel₂ (Δ {S = S}) = funExt λ x → λ i → M-coalg .snd (x .snd .snd (~ i))

---------------------------------
-- Quotienting the delay monad --
---------------------------------

mutual
  data delay≈ {R} : (delay R) -> (delay R) -> Set where
    EqNow : ∀ {r} -> ∀ {b} -> delay≈ (in-fun (inr r , b)) (in-fun (inr r , b))
    EqLater : ∀ {t} -> (∞delay≈ (in-fun (out-fun (t tt))) (in-fun (out-fun (t tt)))) -> delay≈ (in-fun (inl tt , t)) (in-fun (inl tt , t))

  record ∞delay≈ {R} (x : delay R) (y : delay R) : Set where
    coinductive
    field
      force : delay≈ x y

open ∞delay≈

data weak-delay≈ {R} : (delay R) -> (delay R) -> Set where
  EqNow : ∀ {r s} -> r ≡ s -> weak-delay≈ (delay-ret r) (delay-ret s)
  EqLater : ∀ {t u} -> weak-delay≈ t u -> weak-delay≈ (delay-tau t) (delay-tau u)
  EqLaterL : ∀ {t u} -> weak-delay≈ t u -> weak-delay≈ (delay-tau t) u
  EqLaterR : ∀ {t u} -> weak-delay≈ t u -> weak-delay≈ t (delay-tau u)

delay≈-in-out : ∀ {R} {x : delay R} -> delay≈ (in-fun (out-fun x)) (in-fun (out-fun x)) -> delay≈ x x
delay≈-in-out {x = x} = λ p → transp (λ i → delay≈ (funExt⁻ in-inverse-out x i) (funExt⁻ in-inverse-out x i)) i0 p

delay≈-in-out-L : ∀ {R} {x y : delay R} -> delay≈ (in-fun (out-fun x)) y -> delay≈ x y
delay≈-in-out-L {x = x} {y = y} = λ p → transp (λ i → delay≈ (funExt⁻ in-inverse-out x i) y) i0 p

delay≈-in-out-R : ∀ {R} {x y : delay R} -> delay≈ x (in-fun (out-fun y)) -> delay≈ x y
delay≈-in-out-R {x = x} {y = y} = λ p → transp (λ i → delay≈ x (funExt⁻ in-inverse-out y i)) i0 p

{-# OPTIONS --cubical #-}
module Cubical.Data.Nat.Bijections.FinN where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open <-Reasoning
open import Cubical.Tactics.NatSolver
open import Cubical.Data.Nat.Bijections.IncreasingFunction
open import Cubical.Data.Nat.MoreOrderProperties

Finℕ = Σ[ k ∈ ℕ ] Σ[ i ∈ ℕ ] (i ≤ k)

triangle : ℕ → ℕ
triangle zero = zero
triangle (suc n) = n + suc (triangle n)

increasingTriangle : isIncreasing triangle
increasingTriangle = strengthenIncreasing triangle triangleN<triangleSN where
  triangleN<triangleSN : (n : ℕ) → triangle n < triangle (suc n)
  triangleN<triangleSN n = n , refl

private
  1+k+t=k+t+1 : (n : ℕ) → (t : ℕ ) → suc (n + t) ≡ n + suc t
  1+k+t=k+t+1 n t = solveℕ!
  1+k+tk=tsk : (n : ℕ) → suc (n + triangle n) ≡ triangle (suc n)
  1+k+tk=tsk n = 1+k+t=k+t+1 n (triangle n)

  partitionTriangle = partition triangle refl increasingTriangle

  Finℕ≅partitionTriangle : Iso Finℕ partitionTriangle
  Iso.fun Finℕ≅partitionTriangle (k , i , i≤k) = k , i , i+tk<tsk where
      i+tk<tsk : i + triangle k < triangle (suc k)
      i+tk<tsk = i + triangle k <≤⟨ suc-≤-suc (≤-+k {k = triangle k} i≤k) ⟩
                 k + triangle k <≡⟨ <-suc ⟩ 1+k+tk=tsk k

  Iso.inv Finℕ≅partitionTriangle (k , i , i+tk<tsk) = k , i , i≤k where
      i+tk<k+tk+1 : i + triangle k < suc (k + triangle k)
      i+tk<k+tk+1 = i + triangle k <≡⟨ i+tk<tsk ⟩ sym (1+k+tk=tsk k)
      i+tk≤k+tk : i + triangle k ≤ k + triangle k
      i+tk≤k+tk = pred-≤-pred i+tk<k+tk+1
      i≤k : i ≤ k
      i≤k = ≤-+k-cancel i+tk≤k+tk
  Iso.rightInv Finℕ≅partitionTriangle (k , i , _) = ΣPathP (refl , ΣPathPProp (λ _ → isProp≤) refl)
  Iso.leftInv Finℕ≅partitionTriangle  (k , i , _) = ΣPathP (refl , ΣPathPProp (λ _ → isProp≤) refl)

  partitionTriangle≅ℕ : Iso partitionTriangle ℕ
  partitionTriangle≅ℕ = partition≅ℕ triangle refl increasingTriangle

Finℕ≅ℕ : Iso Finℕ ℕ
Finℕ≅ℕ = (compIso Finℕ≅partitionTriangle partitionTriangle≅ℕ)

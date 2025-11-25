module Cubical.Data.Nat.Bijections.Triangle where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open <-Reasoning
open import Cubical.Tactics.NatSolver
open import Cubical.Data.Nat.Bijections.IncreasingFunction

Triangle⊂ℕ×ℕ = Σ[ k ∈ ℕ ] Σ[ i ∈ ℕ ] (i ≤ k)

triangle : ℕ → ℕ
triangle zero = zero
triangle (suc n) = n + suc (triangle n)

strictIncTriangle : isStrictlyIncreasing triangle
strictIncTriangle = sucIncreasing→StrictlyIncreasing triangle triangleN<triangleSN where
  triangleN<triangleSN : (n : ℕ) → triangle n < triangle (suc n)
  triangleN<triangleSN n = n , refl

private
  1+k+tk=tsk : (n : ℕ) → suc (n + triangle n) ≡ triangle (suc n)
  1+k+tk=tsk n = sym (+-suc _ _)

  partitionTriangle = partition triangle refl strictIncTriangle

  Triangle⊂ℕ×ℕ≅partitionTriangle : Iso Triangle⊂ℕ×ℕ partitionTriangle
  Iso.fun Triangle⊂ℕ×ℕ≅partitionTriangle (k , i , i≤k) = k , i , i+tk<tsk where
      i+tk<tsk : i + triangle k < triangle (suc k)
      i+tk<tsk = i + triangle k <≤⟨ suc-≤-suc (≤-+k {k = triangle k} i≤k) ⟩
                 k + triangle k <≡⟨ <-suc ⟩ 1+k+tk=tsk k

  Iso.inv Triangle⊂ℕ×ℕ≅partitionTriangle (k , i , i+tk<tsk) = k , i , i≤k where
      i+tk<k+tk+1 : i + triangle k < suc (k + triangle k)
      i+tk<k+tk+1 = i + triangle k <≡⟨ i+tk<tsk ⟩ sym (1+k+tk=tsk k)
      i+tk≤k+tk : i + triangle k ≤ k + triangle k
      i+tk≤k+tk = pred-≤-pred i+tk<k+tk+1
      i≤k : i ≤ k
      i≤k = ≤-+k-cancel i+tk≤k+tk
  Iso.rightInv Triangle⊂ℕ×ℕ≅partitionTriangle (k , i , _) = ΣPathP (refl , ΣPathPProp (λ _ → isProp≤) refl)
  Iso.leftInv Triangle⊂ℕ×ℕ≅partitionTriangle  (k , i , _) = ΣPathP (refl , ΣPathPProp (λ _ → isProp≤) refl)

  partitionTriangle≅ℕ : Iso partitionTriangle ℕ
  partitionTriangle≅ℕ = partition≅ℕ triangle refl strictIncTriangle

Triangle⊂ℕ×ℕ≅ℕ : Iso Triangle⊂ℕ×ℕ ℕ
Triangle⊂ℕ×ℕ≅ℕ = (compIso Triangle⊂ℕ×ℕ≅partitionTriangle partitionTriangle≅ℕ)

{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Data.FinInd where

open import Cubical.Data.Nat
open import Cubical.Data.Fin
open import Cubical.Data.Sigma
open import Cubical.Data.FinSet
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Functions.Surjection
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.S1

private
  variable
    ℓ : Level
    A : Type ℓ

isFinInd : Type ℓ → Type ℓ
isFinInd A = ∃[ n ∈ ℕ ] Fin n ↠ A

isFinSet→isFinInd : isFinSet A → isFinInd A
isFinSet→isFinInd = PT.rec
  squash
  λ (n , equiv) →
    ∣ n , invEq equiv , section→isSurjection (secEq equiv) ∣

isFinInd-S¹ : isFinInd S¹
isFinInd-S¹ = ∣ 1 , f , isSurjection-f ∣
  where
    f : Fin 1 → S¹
    f _ = base
    isSurjection-f : isSurjection f
    isSurjection-f b = PT.map (λ base≡b → fzero , base≡b) (isConnectedS¹ b)

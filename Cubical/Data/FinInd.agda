{-

Definition of finitely indexed types

A type is finitely indexed if, for some `n`, there merely exists a
surjective function from `Fin n` to it. Note that a type doesn't need
to be a set in order for it to be finitely indexed. For example, the
circle is finitely indexed.

This definition is weaker than `isFinSet`.

-}


module Cubical.Data.FinInd where

open import Cubical.Data.Nat
open import Cubical.Data.SumFin
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
isFinSet→isFinInd h = PT.elim
  (λ _ → squash₁)
  (λ equiv →
    ∣ _ , invEq equiv , section→isSurjection (retEq equiv) ∣₁) (h .snd)

isFinInd-S¹ : isFinInd S¹
isFinInd-S¹ = ∣ 1 , f , isSurjection-f ∣₁
  where
    f : Fin 1 → S¹
    f _ = base
    isSurjection-f : isSurjection f
    isSurjection-f b = PT.map (λ base≡b → fzero , base≡b) (isConnectedS¹ b)

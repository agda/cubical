{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Data.FinSet where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Logic
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Fin

private
  variable
    ℓ : Level
    A : Type ℓ

isFinSet : Type ℓ → Type ℓ
isFinSet A = ∥ Σ[ n ∈ ℕ ] A ≃ Fin n ∥

isProp-isFinSet : isProp (isFinSet A)
isProp-isFinSet = propTruncIsProp

FinSet : Type (ℓ-suc ℓ)
FinSet = TypeWithStr _ isFinSet

isFinSetFin : ∀ {n} → isFinSet (Fin n)
isFinSetFin = ∣ _ , pathToEquiv refl ∣

isFinSetUnit : isFinSet Unit
isFinSetUnit = ∣ 1 , Unit≃Fin1 ∣
  where
    Unit≃Fin1 : Unit ≃ Fin 1
    Unit≃Fin1 =
      isoToEquiv
        (iso
          (const fzero)
          (const tt)
          (isContrFin1 .snd)
          (isContrUnit .snd)
        )

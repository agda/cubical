{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.Interval.NCube where

open import Cubical.Core.Everything

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order

open import Cubical.Data.Vec
open import Cubical.Data.List
open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Cubical.Data.Empty renaming (elim to ⊥-elim ; rec to ⊥-rec )

open import Cubical.Foundations.Everything

open import Cubical.Foundations.CartesianKanOps

open import Cubical.HITs.Interval.Base renaming (elim to I-elim ; rec to I-rec)

NCube : ℕ → Type₀
NCube = λ n → Vec Interval n

corner0 : ∀ {n} →  NCube n
corner0 {zero} = []
corner0 {suc n} =  zero ∷ corner0

corner1 : ∀ {n} →  NCube n
corner1 {zero} = []
corner1 {suc n} =  one ∷ corner1

isPropCube : ∀ {n} → isProp (NCube n)
isPropCube {zero} [] [] i = []
isPropCube {suc n} (x ∷ x₁) (x₂ ∷ x₃) i = (isProp-Interval' x x₂ i) ∷ isPropCube x₁ x₃ i

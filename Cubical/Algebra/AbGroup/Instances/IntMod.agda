{-# OPTIONS --safe #-}
module Cubical.Algebra.AbGroup.Instances.IntMod where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat
open import Cubical.Data.Fin.Arithmetic using (+ₘ-comm)
open import Cubical.Data.Fin

import Cubical.Algebra.Group.Instances.IntMod as Group
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.Int

ℤAbGroup/_ : ℕ → AbGroup (ℓ-zero)
ℤAbGroup/ zero = ℤAbGroup
ℤAbGroup/ (suc n) = Group→AbGroup (Group.ℤGroup/ (suc n)) +ₘ-comm

ℤ/2-elim : ∀ {ℓ} {A : Fin 2 → Type ℓ} → A 0 → A 1 → (x : _) → A x
ℤ/2-elim = Group.ℤ/2-elim

ℤ/2-rec : ∀ {ℓ} {A : Type ℓ} → A → A → Fin 2 → A
ℤ/2-rec = Group.ℤ/2-rec

module _ where
  open AbGroupStr (snd (ℤAbGroup/ 2)) using (-_)
  -Const-ℤ/2 : (x : fst (ℤAbGroup/ 2)) → - x ≡ x
  -Const-ℤ/2 = Group.-Const-ℤ/2

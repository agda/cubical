
module Cubical.Data.Nat.Omniscience where

open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence

open import Cubical.Data.Bool
  renaming (Bool to 𝟚; Bool→Type to ⟨_⟩)
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order.Inductive

open import Cubical.Relation.Nullary

open import Cubical.Axiom.Omniscience

variable
  ℓ : Level
  A : Type ℓ
  F : A → Type ℓ

module _ where
  open Minimal

  never-least→never : (∀ m → ¬ Least F m) → (∀ m → ¬ F m)
  never-least→never ¬LF = wf-elim (flip ∘ curry ∘ ¬LF)

  never→never-least : (∀ m → ¬ F m) → (∀ m → ¬ Least F m)
  never→never-least ¬F m (Fm , _) = ¬F m Fm

  ¬least-wlpo : (∀(P : ℕ → 𝟚) → Dec (∀ x → ¬ Least (⟨_⟩ ∘ P) x)) → WLPO ℕ
  ¬least-wlpo lwlpo P = mapDec never-least→never (_∘ never→never-least) (lwlpo P)

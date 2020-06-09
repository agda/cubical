{-# OPTIONS --cubical --safe #-}

module Cubical.Data.Fin.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)

open import Cubical.Relation.Nullary

-- Finite types.
--
-- Currently it is most convenient to define these as a subtype of the
-- natural numbers, because indexed inductive definitions don't behave
-- well with cubical Agda. This definition also has some more general
-- attractive properties, of course, such as easy conversion back to
-- ℕ.
Fin : ℕ → Type₀
Fin n = Σ[ k ∈ ℕ ] k < n

private
  variable
    ℓ : Level
    k : ℕ

fzero : Fin (suc k)
fzero = (0 , suc-≤-suc zero-≤)

-- It is easy, using this representation, to take the successor of a
-- number as a number in the next largest finite type.
fsuc : Fin k → Fin (suc k)
fsuc (k , l) = (suc k , suc-≤-suc l)

-- Conversion back to ℕ is trivial...
toℕ : Fin k → ℕ
toℕ = fst

-- ... and injective.
toℕ-injective : ∀{fj fk : Fin k} → toℕ fj ≡ toℕ fk → fj ≡ fk
toℕ-injective {fj = fj} {fk} = Σ≡Prop (λ _ → m≤n-isProp)

-- A case analysis helper for induction.
fsplit
  : ∀(fj : Fin (suc k))
  → (fzero ≡ fj) ⊎ (Σ[ fk ∈ Fin k ] fsuc fk ≡ fj)
fsplit (0 , k<sn) = inl (toℕ-injective refl)
fsplit (suc k , k<sn) = inr ((k , pred-≤-pred k<sn) , toℕ-injective refl)

-- Fin 0 is empty
¬Fin0 : ¬ Fin 0
¬Fin0 (k , k<0) = ¬-<-zero k<0

-- The full inductive family eliminator for finite types.
elim
  : ∀(P : ∀{k} → Fin k → Type ℓ)
  → (∀{k} → P {suc k} fzero)
  → (∀{k} {fn : Fin k} → P fn → P (fsuc fn))
  → {k : ℕ} → (fn : Fin k) → P fn
elim P fz fs {zero} = ⊥.rec ∘ ¬Fin0
elim P fz fs {suc k} fj
  = case fsplit fj return (λ _ → P fj) of λ
  { (inl p) → subst P p fz
  ; (inr (fk , p)) → subst P p (fs (elim P fz fs fk))
  }


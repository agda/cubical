{-# OPTIONS --cubical --safe #-}

module Cubical.Data.Fin.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Empty
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sum

open import Cubical.Relation.Nullary

Fin : ℕ → Set
Fin n = Σ[ k ∈ ℕ ] k < n

private
  variable
    ℓ : Level
    k : ℕ

fzero : Fin (suc k)
fzero = (0 , suc-≤-suc zero-≤)

fsuc : Fin k → Fin (suc k)
fsuc (k , l) = (suc k , suc-≤-suc l)

toℕ : Fin k → ℕ
toℕ = fst

toℕ-injective : ∀{fj fk : Fin k} → toℕ fj ≡ toℕ fk → fj ≡ fk
toℕ-injective {fj = fj} {fk} = ΣProp≡ (λ _ → m≤n-isProp)

fsplit
  : ∀(fj : Fin (suc k))
  → (fzero ≡ fj) ⊎ (Σ[ fk ∈ Fin k ] fsuc fk ≡ fj)
fsplit (0 , k<sn) = inl (toℕ-injective refl)
fsplit (suc k , k<sn) = inr ((k , pred-≤-pred k<sn) , toℕ-injective refl)

¬Fin0 : ¬ Fin 0
¬Fin0 (k , k<0) = ¬-<-zero k<0

finduction
  : ∀(P : ∀{k} → Fin k → Set ℓ)
  → (∀{k} → P {suc k} fzero)
  → (∀{k} {fn : Fin k} → P fn → P (fsuc fn))
  → {k : ℕ} → (fn : Fin k) → P fn
finduction P fz fs {zero} = ⊥-elim ∘ ¬Fin0
finduction P fz fs {suc k} fj
  = case fsplit fj return (λ _ → P fj) of λ
  { (inl p) → subst P p fz
  ; (inr (fk , p)) → subst P p (fs (finduction P fz fs fk))
  }


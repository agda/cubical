{-# OPTIONS --safe #-}

module Cubical.Data.SumFin.Properties where

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit
import Cubical.Data.Fin as Fin
open import Cubical.Data.Nat
open import Cubical.Data.SumFin.Base as SumFin
open import Cubical.Data.Sum
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation

private
  variable
    ℓ : Level
    k : ℕ

SumFin→Fin : Fin k → Fin.Fin k
SumFin→Fin = SumFin.elim (λ {k} _ → Fin.Fin k) Fin.fzero Fin.fsuc

Fin→SumFin : Fin.Fin k → Fin k
Fin→SumFin = Fin.elim (λ {k} _ → Fin k) fzero fsuc

Fin→SumFin-fsuc : (fk : Fin.Fin k) → Fin→SumFin (Fin.fsuc fk) ≡ fsuc (Fin→SumFin fk)
Fin→SumFin-fsuc = Fin.elim-fsuc (λ {k} _ → Fin k) fzero fsuc

SumFin→Fin→SumFin : (fk : Fin k) → Fin→SumFin (SumFin→Fin fk) ≡ fk
SumFin→Fin→SumFin = SumFin.elim (λ fk → Fin→SumFin (SumFin→Fin fk) ≡ fk)
                                refl λ {k} {fk} eq →
  Fin→SumFin (Fin.fsuc (SumFin→Fin fk)) ≡⟨ Fin→SumFin-fsuc (SumFin→Fin fk) ⟩
  fsuc (Fin→SumFin (SumFin→Fin fk))     ≡⟨ cong fsuc eq ⟩
  fsuc fk                               ∎

Fin→SumFin→Fin : (fk : Fin.Fin k) → SumFin→Fin (Fin→SumFin fk) ≡ fk
Fin→SumFin→Fin = Fin.elim (λ fk → SumFin→Fin (Fin→SumFin fk) ≡ fk)
                          refl λ {k} {fk} eq →
  SumFin→Fin (Fin→SumFin (Fin.fsuc fk)) ≡⟨ cong SumFin→Fin (Fin→SumFin-fsuc fk) ⟩
  Fin.fsuc (SumFin→Fin (Fin→SumFin fk)) ≡⟨ cong Fin.fsuc eq ⟩
  Fin.fsuc fk                           ∎

SumFin≃Fin : ∀ k → Fin k ≃ Fin.Fin k
SumFin≃Fin _ =
  isoToEquiv (iso SumFin→Fin Fin→SumFin Fin→SumFin→Fin SumFin→Fin→SumFin)

SumFin≡Fin : ∀ k → Fin k ≡ Fin.Fin k
SumFin≡Fin k = ua (SumFin≃Fin k)

-- Closure properties of SumFin under type constructors

private
  _⋆_ = compEquiv

infixr 30 _⋆_

SumFin⊎≃ : (m n : ℕ) → (Fin m ⊎ Fin n) ≃ (Fin (m + n))
SumFin⊎≃ 0 n = ⊎-swap-≃ ⋆ ⊎-⊥-≃
SumFin⊎≃ (suc m) n = ⊎-assoc-≃ ⋆ ⊎-equiv (idEquiv ⊤) (SumFin⊎≃ m n)

SumFinΣ≃ : (n : ℕ)(f : Fin n → ℕ) → (Σ (Fin n) (λ x → Fin (f x))) ≃ (Fin (totalSum f))
SumFinΣ≃ 0 f = ΣEmpty _
SumFinΣ≃ (suc n) f =
    Σ⊎≃
  ⋆ ⊎-equiv (ΣUnit (λ tt → Fin (f (inl tt)))) (SumFinΣ≃ n (λ x → f (inr x)))
  ⋆ SumFin⊎≃ (f (inl tt)) (totalSum (λ x → f (inr x)))

SumFin×≃ : (m n : ℕ) → (Fin m × Fin n) ≃ (Fin (m · n))
SumFin×≃ m n = SumFinΣ≃ m (λ _ → n) ⋆ pathToEquiv (λ i → Fin (totalSumConst {m = m} n i))

SumFinΠ≃ : (n : ℕ)(f : Fin n → ℕ) → ((x : Fin n) → Fin (f x)) ≃ (Fin (totalProd f))
SumFinΠ≃ 0 f = isContr→≃Unit (isContrΠ⊥) ⋆ invEquiv (⊎-⊥-≃)
SumFinΠ≃ (suc n) f =
    Π⊎≃
  ⋆ Σ-cong-equiv (ΠUnit (λ tt → Fin (f (inl tt)))) (λ _ → SumFinΠ≃ n (λ x → f (inr x)))
  ⋆ SumFin×≃ (f (inl tt)) (totalProd (λ x → f (inr x)))

isNotZero : ℕ → ℕ
isNotZero 0 = 0
isNotZero (suc n) = 1

SumFin∥∥≃ : (n : ℕ) → ∥ Fin n ∥ ≃ Fin (isNotZero n)
SumFin∥∥≃ 0 = propTruncIdempotent≃ (isProp⊥)
SumFin∥∥≃ (suc n) =
    isContr→≃Unit (inhProp→isContr ∣ inl tt ∣ isPropPropTrunc)
  ⋆ isContr→≃Unit (isContrUnit) ⋆ invEquiv (⊎-⊥-≃)

{-# OPTIONS --safe #-}

module Cubical.Data.SumFin.Properties where

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence

open import Cubical.Data.Empty as ⊥
import Cubical.Data.Fin as Fin
open import Cubical.Data.Nat
open import Cubical.Data.SumFin.Base as SumFin

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

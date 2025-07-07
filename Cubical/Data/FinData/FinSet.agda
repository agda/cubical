{-# OPTIONS --safe #-}
module Cubical.Data.FinData.FinSet where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

open import Cubical.Data.Fin
  using ()
  renaming (Fin to Finℕ)
open import Cubical.Data.FinData
open import Cubical.Data.Nat as Nat
  using (ℕ ; _+_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.Data.SumFin as SumFin
  using (fzero ; fsuc)
  renaming (Fin to SumFin)
open import Cubical.Data.FinSet

open import Cubical.Relation.Nullary

private
  variable
    ℓ : Level
    m n : ℕ

FinFinℕIso : Iso (Fin n) (Finℕ n)
FinFinℕIso = iso
  (λ k → toℕ k , toℕ<n k)
  (uncurry (fromℕ' _))
  (λ (k , k<n) → Σ≡Prop (λ _ → isProp≤) (toFromId' _ k k<n))
  (λ k → fromToId' _ k (toℕ<n k))

Fin≃Finℕ : Fin n ≃ Finℕ n
Fin≃Finℕ = isoToEquiv FinFinℕIso

FinΣ≃ : (n : ℕ) (m : FinVec ℕ n) → Σ (Fin n) (Fin ∘ m) ≃ Fin (foldrFin _+_ 0 m)
FinΣ≃ n m =
  Σ-cong-equiv SumFin.FinData≃SumFin (λ fn → SumFin.≡→FinData≃SumFin
    (congS m (sym (retIsEq (SumFin.FinData≃SumFin .snd) fn))))
  ∙ₑ SumFin.SumFinΣ≃ n (m ∘ SumFin.SumFin→FinData)
  ∙ₑ invEquiv (SumFin.≡→FinData≃SumFin (sum≡ n m))
  where
  sum≡ : (n : ℕ) (m : FinVec ℕ n) →
    foldrFin _+_ 0 m ≡ SumFin.totalSum (m ∘ SumFin.SumFin→FinData)
  sum≡ = Nat.elim (λ _ → refl) λ n x m → congS (m zero +_) (x (m ∘ suc))

DecΣ : (n : ℕ) →
  (P : FinVec (Type ℓ) n) → (∀ k → Dec (P k)) → Dec (Σ (Fin n) P)
DecΣ n P decP = EquivPresDec
  (Σ-cong-equiv-fst (invEquiv SumFin.FinData≃SumFin))
  (SumFin.DecΣ n (P ∘ SumFin.SumFin→FinData) (decP ∘ SumFin.SumFin→FinData))

isFinSetFinData : ∀ {n} → isFinSet (Fin n)
isFinSetFinData = subst isFinSet (sym SumFin.FinData≡SumFin) isFinSetFin

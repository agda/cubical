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

Fin→SumFin : Fin n → SumFin.Fin n
Fin→SumFin = elim (λ {n} _ → SumFin n) fzero fsuc

SumFin→Fin : SumFin.Fin n → Fin n
SumFin→Fin = SumFin.elim (λ {n} _ → Fin n) zero suc

FinSumFinIso : Iso (Fin n) (SumFin n)
FinSumFinIso = iso Fin→SumFin SumFin→Fin
  (SumFin.elim (λ fn → Fin→SumFin (SumFin→Fin fn) ≡ fn) refl (cong fsuc))
  (elim (λ fn → SumFin→Fin (Fin→SumFin fn) ≡ fn) refl (cong suc))

Fin≃SumFin : Fin n ≃ SumFin n
Fin≃SumFin = isoToEquiv FinSumFinIso

≡→Fin≃SumFin : m ≡ n → Fin m ≃ SumFin n
≡→Fin≃SumFin {m} = J (λ n p → Fin m ≃ SumFin n) Fin≃SumFin

Fin≡SumFin : Fin n ≡ SumFin n
Fin≡SumFin = ua Fin≃SumFin

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
  Σ-cong-equiv Fin≃SumFin (λ fn → ≡→Fin≃SumFin
    (congS m (sym (retIsEq (Fin≃SumFin .snd) fn))))
  ∙ₑ SumFin.SumFinΣ≃ n (m ∘ SumFin→Fin)
  ∙ₑ invEquiv (≡→Fin≃SumFin (sum≡ n m))
  where
  sum≡ : (n : ℕ) (m : FinVec ℕ n) →
    foldrFin _+_ 0 m ≡ SumFin.totalSum (m ∘ SumFin→Fin)
  sum≡ = Nat.elim (λ _ → refl) λ n x m → congS (m zero +_) (x (m ∘ suc))

DecΣ : (n : ℕ) →
  (P : FinVec (Type ℓ) n) → (∀ k → Dec (P k)) → Dec (Σ (Fin n) P)
DecΣ n P decP = EquivPresDec
  (Σ-cong-equiv-fst (invEquiv Fin≃SumFin))
  (SumFin.DecΣ n (P ∘ SumFin→Fin) (decP ∘ SumFin→Fin))

isFinSetFinData : ∀ {n} → isFinSet (Fin n)
isFinSetFinData = subst isFinSet (sym Fin≡SumFin) isFinSetFin

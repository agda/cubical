{-# OPTIONS --cubical #-}
{-# OPTIONS --safe #-}

module Cubical.Algebra.Determinat.Minor where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Algebra.Matrix
open import Cubical.Data.Nat renaming ( _+_ to _+ℕ_ ; _·_ to _·ℕ_
                                       ; +-comm to +ℕ-comm
                                       ; +-assoc to +ℕ-assoc
                                       ; ·-assoc to ·ℕ-assoc)
open import Cubical.Data.Vec.Base using (_∷_; [])
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Data.FinData
open import Cubical.Data.FinData.Order using (_<'Fin_; _≤'Fin_)
open import Cubical.Algebra.Ring
open import Cubical.Algebra.Ring.Base
open import Cubical.Algebra.Ring.BigOps
open import Cubical.Algebra.Monoid.BigOp
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Base
open import Cubical.Data.Nat.Order
open import Cubical.Tactics.CommRingSolver

module Minor (ℓ : Level) where

  -- definition and properties to remove one Index, i.e. (removeIndex i) is the monoton ebbeding from {0,...,n-1} to {0,...,n} ommiting i.
  removeIndex : {n : ℕ} → Fin (suc n) → Fin n → Fin (suc n)
  removeIndex zero k = suc k
  removeIndex (suc i) zero = zero
  removeIndex (suc i) (suc k) = suc (removeIndex i k)

  -- On {0,...,i-1} the map (removeIndex i) is the identity.
  removeIndexId : {n : ℕ} → (i : Fin (suc n)) → (k : Fin n) → (suc k) ≤'Fin i → (removeIndex i k) ≡ weakenFin k
  removeIndexId (suc i) zero le = refl
  removeIndexId (suc i) (suc k) (s≤s le) =  cong (λ a → suc a) (removeIndexId i k le)

  -- On {i,...,n-1} the map (removeIndex i) is the successor function.
  removeIndexSuc : {n : ℕ} → (i : Fin (suc n)) → (k : Fin n) → i ≤'Fin weakenFin k  → (removeIndex i k) ≡ suc k
  removeIndexSuc zero k le = refl
  removeIndexSuc (suc i) (suc k) (s≤s le) = cong (λ a → suc a) (removeIndexSuc i k le)

  -- A formula for commuting removeIndex maps
  removeIndexComm :  {n : ℕ} → (i j : Fin (suc n)) → (k : Fin n) → i ≤'Fin j →
    removeIndex (suc j) (removeIndex i k) ≡ removeIndex (weakenFin i) (removeIndex j k)
  removeIndexComm zero j k le = refl
  removeIndexComm (suc i) (suc j) zero le = refl
  removeIndexComm (suc i) (suc j) (suc k) (s≤s le) =  cong (λ a → suc a) (removeIndexComm i j k le)

  -- remove the j-th column of a matrix

  remove-column : {A : Type ℓ} {n m : ℕ} (j : Fin (suc m)) (M : FinMatrix A n (suc m)) → FinMatrix A n m
  remove-column j M k l = M k (removeIndex j l)

  remove-column-comm :  {A : Type ℓ} {n m : ℕ} (i : Fin (suc m)) (j : Fin (suc m)) (M : FinMatrix A n (suc (suc m))) (k : Fin n) (l : Fin  m) →
    j ≤'Fin i →
    remove-column j (remove-column (suc i) M) k l ≡  remove-column i (remove-column (weakenFin j) M) k l
  remove-column-comm i j M k l le =
    remove-column j (remove-column (suc i) M) k l
    ≡⟨  refl ⟩
     M k (removeIndex (suc i) (removeIndex j l))
    ≡⟨ cong (λ a → M k a) ( removeIndexComm j i l le) ⟩
    M k (removeIndex (weakenFin j) (removeIndex i l))
    ≡⟨ refl ⟩
     remove-column i (remove-column (weakenFin j) M) k l
    ∎

  -- remove the i-th row of a matrix
  remove-row : {A : Type ℓ} {n m : ℕ} (i : Fin (suc n)) (M : FinMatrix A (suc n) m) → FinMatrix A n m
  remove-row i M k l = M (removeIndex i k) l

  remove-row-comm : {A : Type ℓ} {n m : ℕ} (i : Fin (suc n)) (j : Fin (suc n)) (M : FinMatrix A (suc (suc n)) m) (k : Fin n) (l : Fin  m) →
    j ≤'Fin i →
    remove-row j (remove-row (suc i) M) k l ≡  remove-row i (remove-row (weakenFin j) M) k l
  remove-row-comm i j M k l le =
    remove-row j (remove-row (suc i) M) k l
    ≡⟨ refl ⟩
      M (removeIndex (suc i) (removeIndex j k)) l
    ≡⟨ cong (λ a → M a l) ( removeIndexComm j i k le) ⟩
    M (removeIndex (weakenFin j) (removeIndex i k)) l
    ≡⟨ refl ⟩
     remove-row i (remove-row (weakenFin j) M) k l
    ∎

  remove-column-row-comm : {A : Type ℓ} {n m : ℕ}  (i : Fin (suc n)) (j : Fin (suc m)) (M : FinMatrix A (suc n) (suc m)) (k : Fin n) (l : Fin m) →  (remove-row i (remove-column j M)) k l ≡  (remove-column j (remove-row i M)) k l
  remove-column-row-comm i j M k l = refl

  -- Calculating of the minor.
  minor : {A : Type ℓ} {n m : ℕ} (i : Fin (suc n)) (j : Fin (suc m)) (M : FinMatrix A (suc n) (suc m)) → FinMatrix A n m
  minor i j M = remove-column j (remove-row i M)

  -- Compatability of the minor with the equality.
  minorComp : {A : Type ℓ} {n m : ℕ} (i : Fin (suc n)) (j : Fin (suc m)) (M N : FinMatrix A (suc n) (suc m)) → ((i : Fin (suc n)) → (j : Fin (suc m)) → M i j ≡ N i j ) → (k : Fin n) → (l : Fin m) →  minor i j M k l ≡ minor i j N k l
  minorComp {n = suc n} {suc m} i j M N f k l = f (removeIndex i k) (removeIndex j l)

  -- Formulas to commute minors
  minorComm0 : {A : Type ℓ} {n m : ℕ} (i₁ i₂ : Fin (suc n)) (j₁ j₂ : Fin (suc m)) (k : Fin n) (l : Fin m) (M : FinMatrix A (suc (suc n)) (suc (suc m))) →
    i₂ ≤'Fin i₁ → j₂ ≤'Fin j₁ →
    minor i₂ j₂ (minor (suc i₁) (suc j₁) M) k l ≡ minor i₁ j₁ (minor (weakenFin i₂) (weakenFin j₂) M) k l
  minorComm0 i₁ i₂ j₁ j₂ k l M lei lej =
    M (removeIndex (suc i₁) (removeIndex i₂ k))
      (removeIndex (suc j₁) (removeIndex j₂ l))
    ≡⟨ cong (λ a →  M a (removeIndex (suc j₁) (removeIndex j₂ l))) (removeIndexComm i₂ i₁ k lei) ⟩
    M (removeIndex (weakenFin i₂) (removeIndex i₁ k))
      (removeIndex (suc j₁) (removeIndex j₂ l))
    ≡⟨ cong (λ a →  M (removeIndex (weakenFin i₂) (removeIndex i₁ k)) a ) ((removeIndexComm j₂ j₁ l lej)) ⟩
    M (removeIndex (weakenFin i₂) (removeIndex i₁ k))
      (removeIndex (weakenFin j₂) (removeIndex j₁ l))
    ∎

  minorComm1 : {A : Type ℓ} {n m : ℕ} (i₁ i₂ : Fin (suc n)) (j₁ j₂ : Fin (suc m)) (k : Fin n) (l : Fin m) (M : FinMatrix A (suc (suc n)) (suc (suc m))) →
   i₂ ≤'Fin i₁ → j₁ ≤'Fin j₂ →
   minor i₂ j₂ (minor (suc i₁) (weakenFin j₁) M) k l ≡ minor i₁ j₁ (minor (weakenFin i₂) (suc j₂) M) k l

  minorComm1 i₁ i₂ j₁ j₂ k l M lei lej =
    M (removeIndex (suc i₁) (removeIndex i₂ k))
      (removeIndex (weakenFin j₁) (removeIndex j₂ l))
    ≡⟨ cong (λ a → M a (removeIndex (weakenFin j₁) (removeIndex j₂ l))) ((removeIndexComm i₂ i₁ k lei)) ⟩
    M (removeIndex (weakenFin i₂) (removeIndex i₁ k))
      (removeIndex (weakenFin j₁) (removeIndex j₂ l))
    ≡⟨ cong (λ a → M (removeIndex (weakenFin i₂) (removeIndex i₁ k)) a) (sym ((removeIndexComm j₁ j₂ l lej))) ⟩
    M (removeIndex (weakenFin i₂) (removeIndex i₁ k))
      (removeIndex (suc j₂) (removeIndex j₁ l))
    ∎

  minorComm2 : {A : Type ℓ} {n m : ℕ} (i₁ i₂ : Fin (suc n)) (j₁ j₂ : Fin (suc m)) (k : Fin n) (l : Fin m) (M : FinMatrix A (suc (suc n)) (suc (suc m))) →
   i₁ ≤'Fin i₂ → j₂ ≤'Fin j₁ →
   minor i₂ j₂ (minor (weakenFin i₁) (suc j₁) M) k l ≡ minor i₁ j₁ (minor (suc i₂) (weakenFin j₂) M) k l

  minorComm2 i₁ i₂ j₁ j₂ k l M lei lej =
   M (removeIndex (weakenFin i₁) (removeIndex i₂ k))
     (removeIndex (suc j₁) (removeIndex j₂ l))
   ≡⟨ cong (λ a → M a  (removeIndex (suc j₁) (removeIndex j₂ l))) (sym ((removeIndexComm i₁ i₂ k lei))) ⟩
   M (removeIndex (suc i₂) (removeIndex i₁ k))
     (removeIndex (suc j₁) (removeIndex j₂ l))
   ≡⟨ cong (λ a →  M (removeIndex (suc i₂) (removeIndex i₁ k)) a) ((removeIndexComm j₂ j₁ l lej)) ⟩
   M (removeIndex (suc i₂) (removeIndex i₁ k))
     (removeIndex (weakenFin j₂) (removeIndex j₁ l))
   ∎

  minorSemiCommR : {A : Type ℓ} {n m : ℕ} (i₁ : Fin (suc (suc n))) (i₂ : Fin (suc n)) (j₁ j₂ : Fin (suc m)) (k : Fin n) (l : Fin m) (M : FinMatrix A (suc (suc n)) (suc (suc m))) →
   j₂ ≤'Fin j₁ →
   minor i₂ j₂ (minor i₁ (suc j₁) M) k l ≡ minor i₂ j₁ (minor i₁ (weakenFin j₂) M) k l
  minorSemiCommR i₁ i₂ j₁ j₂ k l M lej =
    cong
      (λ a → M (removeIndex i₁ (removeIndex i₂ k)) a)
      (removeIndexComm j₂ j₁ l lej)


  --Formulas to compute compute the entries of the minor.
  minorIdId : {A : Type ℓ} {n m : ℕ} (i : Fin (suc n))(j : Fin (suc m)) (k : Fin n)(l : Fin m) (M : FinMatrix A (suc n) (suc m)) →
    suc k ≤'Fin i → suc l ≤'Fin j →
    minor i j M k l ≡ M (weakenFin k) (weakenFin l)
  minorIdId i j k l M lei lej =
    M  (removeIndex i k) (removeIndex j l)
    ≡⟨ cong (λ a → M a (removeIndex j l)) (removeIndexId i k lei) ⟩
    M (weakenFin k) (removeIndex j l)
    ≡⟨ cong (λ a → M (weakenFin k) a) (removeIndexId j l lej) ⟩
    M (weakenFin k) (weakenFin l)
    ∎

  minorSucSuc : {A : Type ℓ} {n m : ℕ} (i : Fin (suc n))(j : Fin (suc m)) (k : Fin n)(l : Fin m) (M : FinMatrix A (suc n) (suc m)) →
    i ≤'Fin weakenFin k → j ≤'Fin weakenFin l →
    minor i j M k l ≡ M (suc k) (suc l)
  minorSucSuc i j k l M lei lej =
    M  (removeIndex i k) (removeIndex j l)
    ≡⟨ cong (λ a → M a (removeIndex j l)) (removeIndexSuc i k lei) ⟩
    M (suc k) (removeIndex j l)
    ≡⟨ cong (λ a → M (suc k) a) (removeIndexSuc j l lej) ⟩
    M (suc k) (suc l)
    ∎

  minorIdSuc : {A : Type ℓ} {n m : ℕ} (i : Fin (suc n))(j : Fin (suc m)) (k : Fin n)(l : Fin m) (M : FinMatrix A (suc n) (suc m)) →
    suc k ≤'Fin i → j ≤'Fin weakenFin l →
    minor i j M k l ≡ M (weakenFin k) (suc l)
  minorIdSuc i j k l M lei lej =
    M  (removeIndex i k) (removeIndex j l)
    ≡⟨ cong (λ a → M a (removeIndex j l)) (removeIndexId i k lei) ⟩
    M (weakenFin k) (removeIndex j l)
    ≡⟨ cong (λ a → M (weakenFin k) a) (removeIndexSuc j l lej) ⟩
    M (weakenFin k) (suc l)
    ∎

  minorSucId : {A : Type ℓ} {n m : ℕ} (i : Fin (suc n))(j : Fin (suc m)) (k : Fin n)(l : Fin m) (M : FinMatrix A (suc n) (suc m)) →
    i ≤'Fin weakenFin k → suc l ≤'Fin j →
    minor i j M k l ≡ M (suc k) (weakenFin l)
  minorSucId i j k l M lei lej =
    M  (removeIndex i k) (removeIndex j l)
    ≡⟨ cong (λ a → M a (removeIndex j l)) (removeIndexSuc i k lei) ⟩
    M (suc k) (removeIndex j l)
    ≡⟨ cong (λ a → M (suc k) a) (removeIndexId j l lej) ⟩
    M (suc k) (weakenFin l)
    ∎


{-# OPTIONS --cubical --safe #-}
module Cubical.Algebra.Matrix where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat hiding (_+_)
open import Cubical.Data.Vec
open import Cubical.Data.FinData
open import Cubical.Relation.Nullary

open import Cubical.Structures.CommRing

private
  variable
    ℓ : Level


-- Equivalence between Vec matrix and Fin function matrix

FinMatrix : (A : Type ℓ) (m n : ℕ) → Type ℓ
FinMatrix A m n = FinVec (FinVec A n) m

VecMatrix : (A : Type ℓ) (m n : ℕ) → Type ℓ
VecMatrix A m n = Vec (Vec A n) m

FinMatrix≡VecMatrix : (A : Type ℓ) (m n : ℕ) → FinMatrix A m n ≡ VecMatrix A m n
FinMatrix≡VecMatrix A m n i = FinVec≡Vec (FinVec≡Vec A n i) m i


-- Experiment using addition. Transport commutativity from one
-- representation to the the other.
module _ (R : CommRing {ℓ}) where

  open commring-operation-syntax

  -- TODO: how to just use +? Seems to work for AbGroup...
  addFinMatrix : ∀ {m n} → FinMatrix ⟨ R ⟩ m n → FinMatrix ⟨ R ⟩ m n → FinMatrix ⟨ R ⟩ m n
  addFinMatrix M N = λ k l → M k l +⟨ R ⟩ N k l

  addFinMatrixComm : ∀ {m n} → (M N : FinMatrix ⟨ R ⟩ m n) → addFinMatrix M N ≡ addFinMatrix N M
  addFinMatrixComm M N i k l = commring+-comm R (M k l) (N k l) i

  addVecMatrix : ∀ {m n} → VecMatrix ⟨ R ⟩ m n → VecMatrix ⟨ R ⟩ m n → VecMatrix ⟨ R ⟩ m n
  addVecMatrix {m} {n} = transport (λ i → FinMatrix≡VecMatrix ⟨ R ⟩ m n i
                                        → FinMatrix≡VecMatrix ⟨ R ⟩ m n i
                                        → FinMatrix≡VecMatrix ⟨ R ⟩ m n i)
                                   addFinMatrix

  addMatrixPath : ∀ {m n} → PathP (λ i → FinMatrix≡VecMatrix ⟨ R ⟩ m n i
                                       → FinMatrix≡VecMatrix ⟨ R ⟩ m n i
                                       → FinMatrix≡VecMatrix ⟨ R ⟩ m n i)
                                  addFinMatrix addVecMatrix
  addMatrixPath {m} {n} i = transp (λ j → FinMatrix≡VecMatrix ⟨ R ⟩ m n (i ∧ j)
                                        → FinMatrix≡VecMatrix ⟨ R ⟩ m n (i ∧ j)
                                        → FinMatrix≡VecMatrix ⟨ R ⟩ m n (i ∧ j))
                                   (~ i) addFinMatrix

  addVecMatrixComm : ∀ {m n} → (M N : VecMatrix ⟨ R ⟩ m n) → addVecMatrix M N ≡ addVecMatrix N M
  addVecMatrixComm {m} {n} = transport (λ i → (M N : FinMatrix≡VecMatrix ⟨ R ⟩ m n i)
                                            → addMatrixPath i M N ≡ addMatrixPath i N M)
                                       addFinMatrixComm


  -- More direct definition of addition for VecMatrix:

  addVec : ∀ {m} → Vec ⟨ R ⟩ m → Vec ⟨ R ⟩ m → Vec ⟨ R ⟩ m
  addVec [] [] = []
  addVec (x ∷ xs) (y ∷ ys) = x +⟨ R ⟩ y ∷ addVec xs ys

  addVecMatrix' : ∀ {m n} → VecMatrix ⟨ R ⟩ m n → VecMatrix ⟨ R ⟩ m n → VecMatrix ⟨ R ⟩ m n
  addVecMatrix' [] [] = []
  addVecMatrix' (M ∷ MS) (N ∷ NS) = addVec M N ∷ addVecMatrix' MS NS

  -- This proof seems tricky... It might help if transp reduces for Vec
  addVecMatrixEq : ∀ {m n} → (M N : VecMatrix ⟨ R ⟩ m n) → addVecMatrix M N ≡ addVecMatrix' M N
  addVecMatrixEq {zero} {n} [] [] = λ i → foo i
    where
    foo : transport (λ j → Vec (ua (FinVec≃Vec ⟨ R ⟩ n) j) zero) [] ≡ []
    foo = {!!}
  addVecMatrixEq {suc m} {n} (M ∷ MS) (N ∷ NS) = {!!}

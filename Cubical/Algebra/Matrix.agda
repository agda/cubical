{-# OPTIONS --cubical --safe #-}
module Cubical.Algebra.Matrix where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Functions.FunExtEquiv

import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat hiding (_+_)
open import Cubical.Data.Vec
open import Cubical.Data.FinData
open import Cubical.Relation.Nullary

open import Cubical.Structures.CommRing

private
  variable
    ℓ : Level
    A : Type ℓ

-- Equivalence between Vec matrix and Fin function matrix

FinMatrix : (A : Type ℓ) (m n : ℕ) → Type ℓ
FinMatrix A m n = FinVec (FinVec A n) m

VecMatrix : (A : Type ℓ) (m n : ℕ) → Type ℓ
VecMatrix A m n = Vec (Vec A n) m

FinMatrix→VecMatrix : {m n : ℕ} → FinMatrix A m n → VecMatrix A m n
FinMatrix→VecMatrix M = FinVec→Vec (λ fm → FinVec→Vec (λ fn → M fm fn))

VecMatrix→FinMatrix : {m n : ℕ} → VecMatrix A m n → FinMatrix A m n
VecMatrix→FinMatrix M fn fm = lookup fm (lookup fn M)

FinMatrix→VecMatrix→FinMatrix : {m n : ℕ} (M : FinMatrix A m n) → VecMatrix→FinMatrix (FinMatrix→VecMatrix M) ≡ M
FinMatrix→VecMatrix→FinMatrix {m = zero} M = funExt λ f → ⊥.rec (¬Fin0 f)
FinMatrix→VecMatrix→FinMatrix {n = zero} M = funExt₂ λ _ f → ⊥.rec (¬Fin0 f)
FinMatrix→VecMatrix→FinMatrix {m = suc m} {n = suc n} M = funExt₂ goal
  where
  goal : (fm : Fin (suc m)) (fn : Fin (suc n)) →
         VecMatrix→FinMatrix (_ ∷ FinMatrix→VecMatrix (λ z → M (suc z))) fm fn ≡ M fm fn
  goal zero zero = refl
  goal zero (suc fn) i = FinVec→Vec→FinVec (λ z → M zero (suc z)) i fn
  goal (suc fm) fn i = FinMatrix→VecMatrix→FinMatrix (λ z → M (suc z)) i fm fn

VecMatrix→FinMatrix→VecMatrix : {m n : ℕ} (M : VecMatrix A m n) → FinMatrix→VecMatrix (VecMatrix→FinMatrix M) ≡ M
VecMatrix→FinMatrix→VecMatrix {m = zero} [] = refl
VecMatrix→FinMatrix→VecMatrix {m = suc m} (M ∷ MS) i = Vec→FinVec→Vec M i ∷ VecMatrix→FinMatrix→VecMatrix MS i

FinMatrixIsoVecMatrix : (A : Type ℓ) (m n : ℕ) → Iso (FinMatrix A m n) (VecMatrix A m n)
FinMatrixIsoVecMatrix A m n =
  iso FinMatrix→VecMatrix VecMatrix→FinMatrix VecMatrix→FinMatrix→VecMatrix FinMatrix→VecMatrix→FinMatrix

FinMatrix≃VecMatrix : {m n : ℕ} → FinMatrix A m n ≃ VecMatrix A m n
FinMatrix≃VecMatrix {_} {A} {m} {n} = isoToEquiv (FinMatrixIsoVecMatrix A m n)

FinMatrix≡VecMatrix : (A : Type ℓ) (m n : ℕ) → FinMatrix A m n ≡ VecMatrix A m n
FinMatrix≡VecMatrix _ _ _ = ua FinMatrix≃VecMatrix


-- We could have constructed the above Path as follows, but that
-- doesn't reduce as nicely as ua isn't on the toplevel:
--
-- FinMatrix≡VecMatrix : (A : Type ℓ) (m n : ℕ) → FinMatrix A m n ≡ VecMatrix A m n
-- FinMatrix≡VecMatrix A m n i = FinVec≡Vec (FinVec≡Vec A n i) m i


-- Experiment using addition. Transport commutativity from one
-- representation to the the other and relate the transported
-- operation with a more direct definition.
module _ (R : CommRing {ℓ}) where

  open commring-·syntax R

  addFinMatrix : ∀ {m n} → FinMatrix ⟨ R ⟩ m n → FinMatrix ⟨ R ⟩ m n → FinMatrix ⟨ R ⟩ m n
  addFinMatrix M N = λ k l → M k l + N k l

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
  addVec (x ∷ xs) (y ∷ ys) = x + y ∷ addVec xs ys

  addVecLem : ∀ {m} → (M N : Vec ⟨ R ⟩ m)
            → FinVec→Vec (λ l → lookup l M + lookup l N) ≡ addVec M N
  addVecLem {zero} [] [] = refl
  addVecLem {suc m} (x ∷ xs) (y ∷ ys) = cong (λ zs → x + y ∷ zs) (addVecLem xs ys)

  addVecMatrix' : ∀ {m n} → VecMatrix ⟨ R ⟩ m n → VecMatrix ⟨ R ⟩ m n → VecMatrix ⟨ R ⟩ m n
  addVecMatrix' [] [] = []
  addVecMatrix' (M ∷ MS) (N ∷ NS) = addVec M N ∷ addVecMatrix' MS NS

  -- The key lemma relating addVecMatrix and addVecMatrix'
  addVecMatrixEq : ∀ {m n} → (M N : VecMatrix ⟨ R ⟩ m n) → addVecMatrix M N ≡ addVecMatrix' M N
  addVecMatrixEq {zero} {n} [] [] j = transp (λ i → Vec (Vec ⟨ R ⟩ n) 0) j []
  addVecMatrixEq {suc m} {n} (M ∷ MS) (N ∷ NS) =
    addVecMatrix (M ∷ MS) (N ∷ NS)
      ≡⟨ transportUAop₂ FinMatrix≃VecMatrix addFinMatrix (M ∷ MS) (N ∷ NS) ⟩
    FinVec→Vec (λ l → lookup l M + lookup l N) ∷ _
      ≡⟨ (λ i → addVecLem M N i ∷ FinMatrix→VecMatrix (λ k l → lookup l (lookup k MS) + lookup l (lookup k NS))) ⟩
    addVec M N ∷ _
      ≡⟨ cong (λ X → addVec M N ∷ X) (sym (transportUAop₂ FinMatrix≃VecMatrix addFinMatrix MS NS) ∙ addVecMatrixEq MS NS) ⟩
    addVec M N ∷ addVecMatrix' MS NS ∎

  -- By binary funext we get an equality as functions
  addVecMatrixEqFun : ∀ {m} {n} → addVecMatrix {m} {n} ≡ addVecMatrix'
  addVecMatrixEqFun i M N = addVecMatrixEq M N i

  -- We then directly get the properties about addVecMatrix'
  addVecMatrixComm' : ∀ {m n} → (M N : VecMatrix ⟨ R ⟩ m n) → addVecMatrix' M N ≡ addVecMatrix' N M
  addVecMatrixComm' M N = sym (addVecMatrixEq M N) ∙∙ addVecMatrixComm M N ∙∙ addVecMatrixEq N M

  -- TODO: prove more properties about addition of matrices for both
  -- FinMatrix and VecMatrix



-- TODO: define multiplication of matrices and do the same kind of
-- reasoning as we did for addition

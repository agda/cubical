{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.Matrix where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Functions.FunExtEquiv

import Cubical.Data.Empty as ⊥
open import Cubical.Data.Bool
open import Cubical.Data.Nat hiding (_+_ ; +-comm ; +-assoc)
open import Cubical.Data.Vec
open import Cubical.Data.Sigma.Base
open import Cubical.Data.FinData
open import Cubical.Relation.Nullary

open import Cubical.Structures.Group hiding (⟨_⟩)
open import Cubical.Structures.AbGroup hiding (⟨_⟩)
open import Cubical.Structures.Monoid hiding (⟨_⟩)
open import Cubical.Structures.Ring

open Iso

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
FinMatrix→VecMatrix M = FinVec→Vec (λ fm → FinVec→Vec (M fm))

VecMatrix→FinMatrix : {m n : ℕ} → VecMatrix A m n → FinMatrix A m n
VecMatrix→FinMatrix M fn fm = lookup fm (lookup fn M)

FinMatrix→VecMatrix→FinMatrix : {m n : ℕ} (M : FinMatrix A m n)
                              → VecMatrix→FinMatrix (FinMatrix→VecMatrix M) ≡ M
FinMatrix→VecMatrix→FinMatrix {m = zero} M = funExt (⊥.rec ∘ ¬Fin0)
FinMatrix→VecMatrix→FinMatrix {n = zero} M = funExt₂ (λ _ → ⊥.rec ∘ ¬Fin0)
FinMatrix→VecMatrix→FinMatrix {m = suc m} {n = suc n} M = funExt₂ goal
  where
  goal : (fm : Fin (suc m)) (fn : Fin (suc n))
       → VecMatrix→FinMatrix (_ ∷ FinMatrix→VecMatrix (M ∘ suc)) fm fn ≡ M fm fn
  goal zero zero       = refl
  goal zero (suc fn) i = FinVec→Vec→FinVec (M zero ∘ suc) i fn
  goal (suc fm) fn i   = FinMatrix→VecMatrix→FinMatrix (M ∘ suc) i fm fn

VecMatrix→FinMatrix→VecMatrix : {m n : ℕ} (M : VecMatrix A m n)
                              → FinMatrix→VecMatrix (VecMatrix→FinMatrix M) ≡ M
VecMatrix→FinMatrix→VecMatrix {m = zero} [] = refl
VecMatrix→FinMatrix→VecMatrix {m = suc m} (M ∷ MS) i =
  Vec→FinVec→Vec M i ∷ VecMatrix→FinMatrix→VecMatrix MS i

FinMatrixIsoVecMatrix : (A : Type ℓ) (m n : ℕ) → Iso (FinMatrix A m n) (VecMatrix A m n)
fun (FinMatrixIsoVecMatrix A m n)      = FinMatrix→VecMatrix
inv (FinMatrixIsoVecMatrix A m n)      = VecMatrix→FinMatrix
rightInv (FinMatrixIsoVecMatrix A m n) = VecMatrix→FinMatrix→VecMatrix
leftInv (FinMatrixIsoVecMatrix A m n)  = FinMatrix→VecMatrix→FinMatrix

FinMatrix≃VecMatrix : {m n : ℕ} → FinMatrix A m n ≃ VecMatrix A m n
FinMatrix≃VecMatrix {_} {A} {m} {n} = isoToEquiv (FinMatrixIsoVecMatrix A m n)

FinMatrix≡VecMatrix : (A : Type ℓ) (m n : ℕ) → FinMatrix A m n ≡ VecMatrix A m n
FinMatrix≡VecMatrix _ _ _ = ua FinMatrix≃VecMatrix


-- We could have constructed the above Path as follows, but that
-- doesn't reduce as nicely as ua isn't on the toplevel:
--
-- FinMatrix≡VecMatrix : (A : Type ℓ) (m n : ℕ) → FinMatrix A m n ≡ VecMatrix A m n
-- FinMatrix≡VecMatrix A m n i = FinVec≡Vec (FinVec≡Vec A n i) m i

module _ (R' : Ring {ℓ}) where

  open Ring R' renaming ( Carrier to R ; is-set to isSetR )
  open theory R'

  zeroFinMatrix : ∀ {m n} → FinMatrix R m n
  zeroFinMatrix _ _ = 0r

  negFinMatrix : ∀ {m n} → FinMatrix R m n → FinMatrix R m n
  negFinMatrix M i j = - M i j

  addFinMatrix : ∀ {m n} → FinMatrix R m n → FinMatrix R m n → FinMatrix R m n
  addFinMatrix M N i j = M i j + N i j

  oneFinMatrix : ∀ {n} → FinMatrix R n n
  oneFinMatrix i j = if i == j then 1r else 0r

  -- TODO: upstream
  ∑ : ∀ {n} → FinVec R n → R
  ∑ = foldrFin _+_ 0r

  sumVecExt : ∀ {n} → {V W : FinVec R n} → ((i : Fin n) → V i ≡ W i) → ∑ V ≡ ∑ W
  sumVecExt {n = zero} _    = refl
  sumVecExt {n = suc n} h i = h zero i + sumVecExt (h ∘ suc) i

  sumVecSplit : ∀ {n} → (V W : FinVec R n) → ∑ (λ i → V i + W i) ≡ ∑ V + ∑ W
  sumVecSplit {n = zero}  V W = sym (+-rid 0r)
  sumVecSplit {n = suc n} V W =
    V zero + W zero + ∑ (λ i → V (suc i) + W (suc i)) ≡⟨ (λ i → V zero + W zero + sumVecSplit (V ∘ suc) (W ∘ suc) i) ⟩
    V zero + W zero + (∑ (V ∘ suc) + ∑ (W ∘ suc))     ≡⟨ sym (+-assoc _ _ _) ⟩
    V zero + (W zero + (∑ (V ∘ suc) + ∑ (W ∘ suc)))   ≡⟨ cong (λ x → V zero + x) (+-assoc-comm1 _ _ _) ⟩
    V zero + (∑ (V ∘ suc) + (W zero + (∑ (W ∘ suc)))) ≡⟨ +-assoc _ _ _ ⟩
    V zero + ∑ (V ∘ suc) + (W zero + ∑ (W ∘ suc))     ∎

  -- TODO: generalize to sum of n arbitrary elements
  sumVec0r : (n : ℕ) → ∑ (λ (i : Fin n) → 0r) ≡ 0r
  sumVec0r zero    = refl
  sumVec0r (suc n) = cong (λ x → 0r + x) (sumVec0r n) ∙ +-rid 0r

  sumVecExchange : ∀ {m n} → (M : FinMatrix R m n) → ∑ (λ i → ∑ (λ j → M i j)) ≡ ∑ (λ j → ∑ (λ i → M i j))
  sumVecExchange {m = zero}  {n = n}     M = sym (sumVec0r n)
  sumVecExchange {m = suc m} {n = zero}  M = cong (λ x → 0r + x) (sumVec0r m) ∙ +-rid 0r
  sumVecExchange {m = suc m} {n = suc n} M =
     let a  = M zero zero
         L  = ∑ λ j → M zero (suc j)
         C  = ∑ λ i → M (suc i) zero
         N  = ∑ λ i → ∑ λ j → M (suc i) (suc j)
         -- N reindexed
         N' = ∑ λ j → ∑ λ i → M (suc i) (suc j)
     in a + L + ∑ (λ i → ∑ (λ j → M (suc i) j)) ≡⟨ (λ k → a + L + sumVecSplit (λ i → M (suc i) zero) (λ i → ∑ (λ j → M (suc i) (suc j))) k) ⟩
        a + L + (C + N)                         ≡⟨ (λ k → a + L + (C + sumVecExchange (λ i j → M (suc i) (suc j)) k)) ⟩
        a + L + (C + N')                        ≡⟨ sym (+-assoc _ _ _) ⟩
        a + (L + (C + N'))                      ≡⟨ (λ k → a + +-assoc-comm1 L C N' k) ⟩
        a + (C + (L + N'))                      ≡⟨ +-assoc _ _ _ ⟩
        a + C + (L + N')                        ≡⟨ (λ k → a + C + sumVecSplit (λ j → M zero (suc j)) (λ j → ∑ (λ i → M (suc i) (suc j))) (~ k)) ⟩
        a + C + ∑ (λ j → ∑ (λ i → M i (suc j))) ∎

  sumVecMulrdist : ∀ {n} → (x : R) → (V : FinVec R n)
                 → x · ∑ V ≡ ∑ λ i → x · V i
  sumVecMulrdist {n = zero}  x _ = 0-rightNullifies x
  sumVecMulrdist {n = suc n} x V =
    x · (V zero + ∑ (V ∘ suc))           ≡⟨ ·-rdist-+ _ _ _ ⟩
    x · V zero + x · ∑ (V ∘ suc)         ≡⟨ (λ i → x · V zero + sumVecMulrdist x (V ∘ suc) i) ⟩
    x · V zero + ∑ (λ i → x · V (suc i)) ∎

  sumVecMulldist : ∀ {n} → (x : R) → (V : FinVec R n)
                 → (∑ V) · x ≡ ∑ λ i → V i · x
  sumVecMulldist {n = zero}  x _ = 0-leftNullifies x
  sumVecMulldist {n = suc n} x V =
    (V zero + ∑ (V ∘ suc)) · x           ≡⟨ ·-ldist-+ _ _ _ ⟩
    V zero · x + (∑ (V ∘ suc)) · x       ≡⟨ (λ i → V zero · x + sumVecMulldist x (V ∘ suc) i) ⟩
    V zero · x + ∑ (λ i → V (suc i) · x) ∎

  sumVecMulr0 : ∀ {n} → (V : FinVec R n) → ∑ (λ i → V i · 0r) ≡ 0r
  sumVecMulr0 V = sym (sumVecMulldist 0r V) ∙ 0-rightNullifies _

  sumVecMul0r : ∀ {n} → (V : FinVec R n) → ∑ (λ i → 0r · V i) ≡ 0r
  sumVecMul0r V = sym (sumVecMulrdist 0r V) ∙ 0-leftNullifies _

  sumVecMulr1 : (n : ℕ) (V : FinVec R n) → (j : Fin n) → ∑ (λ i → V i · (if i == j then 1r else 0r)) ≡ V j
  sumVecMulr1 (suc n) V zero = (λ k → ·-rid (V zero) k + sumVecMulr0 (V ∘ suc) k) ∙ +-rid (V zero)
  sumVecMulr1 (suc n) V (suc j) =
     (λ i → 0-rightNullifies (V zero) i + ∑ (λ x → V (suc x) · (if x == j then 1r else 0r)))
     ∙∙ +-lid _ ∙∙ sumVecMulr1 n (V ∘ suc) j

  sumVecMul1r : (n : ℕ) (V : FinVec R n) → (j : Fin n) → ∑ (λ i → (if j == i then 1r else 0r) · V i) ≡ V j
  sumVecMul1r (suc n) V zero = (λ k → ·-lid (V zero) k + sumVecMul0r (V ∘ suc) k) ∙ +-rid (V zero)
  sumVecMul1r (suc n) V (suc j) =
    (λ i → 0-leftNullifies (V zero) i + ∑ (λ i → (if j == i then 1r else 0r) · V (suc i)))
    ∙∙ +-lid _ ∙∙ sumVecMul1r n (V ∘ suc) j

  mulFinMatrix : ∀ {m1 m2 m3} → FinMatrix R m1 m2 → FinMatrix R m2 m3 → FinMatrix R m1 m3
  mulFinMatrix M N i k = ∑ λ j → M i j · N j k

  -- Properties
  isSetFinMatrix : ∀ {m n} → isSet (FinMatrix R m n)
  isSetFinMatrix = isSetΠ2 λ _ _ → isSetR

  addFinMatrixAssoc : ∀ {m n} → (M N K : FinMatrix R m n)
                    → addFinMatrix M (addFinMatrix N K) ≡ addFinMatrix (addFinMatrix M N) K
  addFinMatrixAssoc M N K i j k = +-assoc (M j k) (N j k) (K j k) i

  addFinMatrix0r : ∀ {m n} → (M : FinMatrix R m n) → addFinMatrix M zeroFinMatrix ≡ M
  addFinMatrix0r M i j k = +-rid (M j k) i

  addFinMatrix0l : ∀ {m n} → (M : FinMatrix R m n) → addFinMatrix zeroFinMatrix M ≡ M
  addFinMatrix0l M i j k = +-lid (M j k) i

  addFinMatrixNegMatrixr : ∀ {m n} → (M : FinMatrix R m n) → addFinMatrix M (negFinMatrix M) ≡ zeroFinMatrix
  addFinMatrixNegMatrixr M i j k = +-rinv (M j k) i

  addFinMatrixNegMatrixl : ∀ {m n} → (M : FinMatrix R m n) → addFinMatrix (negFinMatrix M) M ≡ zeroFinMatrix
  addFinMatrixNegMatrixl M i j k = +-linv (M j k) i

  addFinMatrixComm : ∀ {m n} → (M N : FinMatrix R m n) → addFinMatrix M N ≡ addFinMatrix N M
  addFinMatrixComm M N i k l = +-comm (M k l) (N k l) i

  mulFinMatrixAssoc : ∀ {m n k l} → (M : FinMatrix R m n) → (N : FinMatrix R n k) → (K : FinMatrix R k l)
                   → mulFinMatrix M (mulFinMatrix N K) ≡ mulFinMatrix (mulFinMatrix M N) K
  mulFinMatrixAssoc M N K = funExt₂ λ i j →
    ∑ (λ k → M i k · ∑ (λ l → N k l · K l j))   ≡⟨ sumVecExt (λ k → sumVecMulrdist (M i k) (λ l → N k l · K l j)) ⟩
    ∑ (λ k → ∑ (λ l → M i k · (N k l · K l j))) ≡⟨ sumVecExt (λ k → sumVecExt (λ l → ·-assoc (M i k) (N k l) (K l j))) ⟩
    ∑ (λ k → ∑ (λ l → M i k · N k l · K l j))   ≡⟨ sumVecExchange (λ k l → M i k · N k l · K l j) ⟩
    ∑ (λ l → ∑ (λ k → M i k · N k l · K l j))   ≡⟨ sumVecExt (λ l → sym (sumVecMulldist (K l j) (λ k → M i k · N k l))) ⟩
    ∑ (λ l → ∑ (λ k → M i k · N k l) · K l j)   ∎

  mulFinMatrixr1 : ∀ {m n} → (M : FinMatrix R m n) → mulFinMatrix M oneFinMatrix ≡ M
  mulFinMatrixr1 M = funExt₂ λ i j → sumVecMulr1 _ (M i) j

  mulFinMatrix1r : ∀ {m n} → (M : FinMatrix R m n) → mulFinMatrix oneFinMatrix M ≡ M
  mulFinMatrix1r M = funExt₂ λ i j → sumVecMul1r _ (λ x → M x j) i

  mulFinMatrixrDistrAddFinMatrix : ∀ {n} (M N K : FinMatrix R n n)
                                 → mulFinMatrix M (addFinMatrix N K) ≡ addFinMatrix (mulFinMatrix M N) (mulFinMatrix M K)
  mulFinMatrixrDistrAddFinMatrix M N K = funExt₂ λ i j →
    ∑ (λ k → M i k · (N k j + K k j))                 ≡⟨ sumVecExt (λ k → ·-rdist-+ (M i k) (N k j) (K k j)) ⟩
    ∑ (λ k → M i k · N k j + M i k · K k j)           ≡⟨ sumVecSplit (λ k → M i k · N k j) (λ k → M i k · K k j) ⟩
    ∑ (λ k → M i k · N k j) + ∑ (λ k → M i k · K k j) ∎

  mulFinMatrixlDistrAddFinMatrix : ∀ {n} (M N K : FinMatrix R n n)
                                 → mulFinMatrix (addFinMatrix M N) K ≡ addFinMatrix (mulFinMatrix M K) (mulFinMatrix N K)
  mulFinMatrixlDistrAddFinMatrix M N K = funExt₂ λ i j →
    ∑ (λ k → (M i k + N i k) · K k j)                 ≡⟨ sumVecExt (λ k → ·-ldist-+ (M i k) (N i k) (K k j)) ⟩
    ∑ (λ k → M i k · K k j + N i k · K k j)           ≡⟨ sumVecSplit (λ k → M i k · K k j) (λ k → N i k · K k j) ⟩
    ∑ (λ k → M i k · K k j) + ∑ (λ k → N i k · K k j) ∎

  FinMatrixRing : (n : ℕ) → Ring {ℓ}
  FinMatrixRing n = makeRing {R = FinMatrix R n n} zeroFinMatrix oneFinMatrix addFinMatrix mulFinMatrix
                          negFinMatrix isSetFinMatrix addFinMatrixAssoc addFinMatrix0r addFinMatrixNegMatrixr addFinMatrixComm
                          mulFinMatrixAssoc mulFinMatrixr1 mulFinMatrix1r mulFinMatrixrDistrAddFinMatrix mulFinMatrixlDistrAddFinMatrix

-- Experiment using addition. Transport commutativity from one
-- representation to the the other and relate the transported
-- operation with a more direct definition.
module _ (R' : Ring {ℓ}) where

  open Ring R' renaming ( Carrier to R )

  addVecMatrix : ∀ {m n} → VecMatrix R m n → VecMatrix R m n → VecMatrix R m n
  addVecMatrix {m} {n} = transport (λ i → FinMatrix≡VecMatrix R m n i
                                        → FinMatrix≡VecMatrix R m n i
                                        → FinMatrix≡VecMatrix R m n i)
                                   (addFinMatrix R')

  addMatrixPath : ∀ {m n} → PathP (λ i → FinMatrix≡VecMatrix R m n i
                                       → FinMatrix≡VecMatrix R m n i
                                       → FinMatrix≡VecMatrix R m n i)
                                  (addFinMatrix R') addVecMatrix
  addMatrixPath {m} {n} i = transp (λ j → FinMatrix≡VecMatrix R m n (i ∧ j)
                                        → FinMatrix≡VecMatrix R m n (i ∧ j)
                                        → FinMatrix≡VecMatrix R m n (i ∧ j))
                                   (~ i) (addFinMatrix R')

  addVecMatrixComm : ∀ {m n} → (M N : VecMatrix R m n) → addVecMatrix M N ≡ addVecMatrix N M
  addVecMatrixComm {m} {n} = transport (λ i → (M N : FinMatrix≡VecMatrix R m n i)
                                            → addMatrixPath i M N ≡ addMatrixPath i N M)
                                       (addFinMatrixComm R')


  -- More direct definition of addition for VecMatrix:

  addVec : ∀ {m} → Vec R m → Vec R m → Vec R m
  addVec [] [] = []
  addVec (x ∷ xs) (y ∷ ys) = x + y ∷ addVec xs ys

  addVecLem : ∀ {m} → (M N : Vec R m)
            → FinVec→Vec (λ l → lookup l M + lookup l N) ≡ addVec M N
  addVecLem {zero} [] [] = refl
  addVecLem {suc m} (x ∷ xs) (y ∷ ys) = cong (λ zs → x + y ∷ zs) (addVecLem xs ys)

  addVecMatrix' : ∀ {m n} → VecMatrix R m n → VecMatrix R m n → VecMatrix R m n
  addVecMatrix' [] [] = []
  addVecMatrix' (M ∷ MS) (N ∷ NS) = addVec M N ∷ addVecMatrix' MS NS

  -- The key lemma relating addVecMatrix and addVecMatrix'
  addVecMatrixEq : ∀ {m n} → (M N : VecMatrix R m n) → addVecMatrix M N ≡ addVecMatrix' M N
  addVecMatrixEq {zero} {n} [] [] j = transp (λ i → Vec (Vec R n) 0) j []
  addVecMatrixEq {suc m} {n} (M ∷ MS) (N ∷ NS) =
    addVecMatrix (M ∷ MS) (N ∷ NS)
      ≡⟨ transportUAop₂ FinMatrix≃VecMatrix (addFinMatrix R') (M ∷ MS) (N ∷ NS) ⟩
    FinVec→Vec (λ l → lookup l M + lookup l N) ∷ _
      ≡⟨ (λ i → addVecLem M N i ∷ FinMatrix→VecMatrix (λ k l → lookup l (lookup k MS) + lookup l (lookup k NS))) ⟩
    addVec M N ∷ _
      ≡⟨ cong (λ X → addVec M N ∷ X) (sym (transportUAop₂ FinMatrix≃VecMatrix (addFinMatrix R') MS NS) ∙ addVecMatrixEq MS NS) ⟩
    addVec M N ∷ addVecMatrix' MS NS ∎

  -- By binary funext we get an equality as functions
  addVecMatrixEqFun : ∀ {m} {n} → addVecMatrix {m} {n} ≡ addVecMatrix'
  addVecMatrixEqFun i M N = addVecMatrixEq M N i

  -- We then directly get the properties about addVecMatrix'
  addVecMatrixComm' : ∀ {m n} → (M N : VecMatrix R m n) → addVecMatrix' M N ≡ addVecMatrix' N M
  addVecMatrixComm' M N = sym (addVecMatrixEq M N) ∙∙ addVecMatrixComm M N ∙∙ addVecMatrixEq N M

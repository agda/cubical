{-# OPTIONS --safe #-}
module Cubical.Algebra.Matrix where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport
open import Cubical.Functions.FunExtEquiv

import Cubical.Data.Empty as ⊥
open import Cubical.Data.Bool
open import Cubical.Data.Nat renaming ( _+_ to _+ℕ_ ; _·_ to _·ℕ_
                                       ; +-comm to +ℕ-comm
                                       ; +-assoc to +ℕ-assoc
                                       ; ·-assoc to ·ℕ-assoc)
open import Cubical.Data.Vec
open import Cubical.Data.Sigma.Base
open import Cubical.Data.FinData
open import Cubical.Relation.Nullary

open import Cubical.Algebra.Group
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Ring
open import Cubical.Algebra.Ring.BigOps
open import Cubical.Algebra.CommRing

open Iso

private
  variable
    ℓ ℓ' : Level
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

-- Define abelian group structure on matrices
module FinMatrixAbGroup (G' : AbGroup ℓ) where

  open AbGroupStr (snd G') renaming ( is-set to isSetG )
  private G = ⟨ G' ⟩

  zeroFinMatrix : ∀ {m n} → FinMatrix G m n
  zeroFinMatrix _ _ = 0g

  negFinMatrix : ∀ {m n} → FinMatrix G m n → FinMatrix G m n
  negFinMatrix M i j = - M i j

  addFinMatrix : ∀ {m n} → FinMatrix G m n → FinMatrix G m n → FinMatrix G m n
  addFinMatrix M N i j = M i j + N i j

  isSetFinMatrix : ∀ {m n} → isSet (FinMatrix G m n)
  isSetFinMatrix = isSetΠ2 λ _ _ → isSetG

  addFinMatrixAssoc : ∀ {m n} → (M N K : FinMatrix G m n)
                    → addFinMatrix M (addFinMatrix N K) ≡ addFinMatrix (addFinMatrix M N) K
  addFinMatrixAssoc M N K i j k = assoc (M j k) (N j k) (K j k) i

  addFinMatrix0r : ∀ {m n} → (M : FinMatrix G m n)
                 → addFinMatrix M zeroFinMatrix ≡ M
  addFinMatrix0r M i j k = rid (M j k) i

  addFinMatrix0l : ∀ {m n} → (M : FinMatrix G m n)
                 → addFinMatrix zeroFinMatrix M ≡ M
  addFinMatrix0l M i j k = lid (M j k) i

  addFinMatrixNegMatrixr : ∀ {m n} → (M : FinMatrix G m n)
                         → addFinMatrix M (negFinMatrix M) ≡ zeroFinMatrix
  addFinMatrixNegMatrixr M i j k = invr (M j k) i

  addFinMatrixNegMatrixl : ∀ {m n} → (M : FinMatrix G m n)
                         → addFinMatrix (negFinMatrix M) M ≡ zeroFinMatrix
  addFinMatrixNegMatrixl M i j k = invl (M j k) i

  addFinMatrixComm : ∀ {m n} → (M N : FinMatrix G m n)
                   → addFinMatrix M N ≡ addFinMatrix N M
  addFinMatrixComm M N i k l = comm (M k l) (N k l) i

  FinMatrixAbGroup : (m n : ℕ) → AbGroup ℓ
  FinMatrixAbGroup m n =
    makeAbGroup {G = FinMatrix G m n} zeroFinMatrix addFinMatrix negFinMatrix
                isSetFinMatrix addFinMatrixAssoc addFinMatrix0r
                addFinMatrixNegMatrixr addFinMatrixComm


-- Define a abelian group structure on vector matrices and prove that
-- it is equal to FinMatrixAbGroup using the SIP
module _ (G' : AbGroup ℓ) where

  open AbGroupStr (snd G')
  private G = ⟨ G' ⟩
  zeroVecMatrix : ∀ {m n} → VecMatrix G m n
  zeroVecMatrix = replicate (replicate 0g)

  negVecMatrix : ∀ {m n} → VecMatrix G m n → VecMatrix G m n
  negVecMatrix = map (map (λ x → - x))

  addVec : ∀ {m} → Vec G m → Vec G m → Vec G m
  addVec [] [] = []
  addVec (x ∷ xs) (y ∷ ys) = x + y ∷ addVec xs ys

  addVecMatrix : ∀ {m n} → VecMatrix G m n → VecMatrix G m n → VecMatrix G m n
  addVecMatrix [] [] = []
  addVecMatrix (M ∷ MS) (N ∷ NS) = addVec M N ∷ addVecMatrix MS NS

  open FinMatrixAbGroup

  -- Proof that FinMatrix→VecMatrix is a group homorphism
  FinMatrix→VecMatrixHomAdd : (m n : ℕ) (M N : FinMatrix G m n)
    → FinMatrix→VecMatrix (addFinMatrix G' M N) ≡
      addVecMatrix (FinMatrix→VecMatrix M) (FinMatrix→VecMatrix N)
  FinMatrix→VecMatrixHomAdd zero n M N = refl
  FinMatrix→VecMatrixHomAdd (suc m) n M N =
    λ i → lem n (M zero) (N zero) i
        ∷ FinMatrix→VecMatrixHomAdd m n (λ i j → M (suc i) j) (λ i j → N (suc i) j) i
     where
     lem : (n : ℕ) (V W : FinVec G n)
       → FinVec→Vec (λ j → V j + W j) ≡ addVec (FinVec→Vec V) (FinVec→Vec W)
     lem zero V W = refl
     lem (suc n) V W = λ i → V zero + W zero ∷ lem n (V ∘ suc) (W ∘ suc) i

  -- Combine everything to get an induced abelian group structure of
  -- VecMatrix that is equal to the one on FinMatrix
  VecMatrixAbGroup : (m n : ℕ) → AbGroup ℓ
  VecMatrixAbGroup m n =
    InducedAbGroup (FinMatrixAbGroup G' m n) addVecMatrix
      FinMatrix≃VecMatrix (FinMatrix→VecMatrixHomAdd m n)

  FinMatrixAbGroup≡VecMatrixAbGroup : (m n : ℕ) → FinMatrixAbGroup G' m n ≡ VecMatrixAbGroup m n
  FinMatrixAbGroup≡VecMatrixAbGroup m n =
    InducedAbGroupPath (FinMatrixAbGroup G' m n) addVecMatrix
      FinMatrix≃VecMatrix (FinMatrix→VecMatrixHomAdd m n)


-- Define identity matrix and matrix multiplication for FinMatrix and
-- prove that square matrices form a ring
module _ (R' : Ring ℓ) where

  open RingStr (snd R') renaming ( is-set to isSetR )
  open RingTheory R'
  open KroneckerDelta R'
  open Sum R'
  open FinMatrixAbGroup (_ , abgroupstr _ _ _ (snd R' .RingStr.+IsAbGroup))

  private R = ⟨ R' ⟩

  oneFinMatrix : ∀ {n} → FinMatrix R n n
  oneFinMatrix i j = δ i j

  mulFinMatrix : ∀ {m1 m2 m3} → FinMatrix R m1 m2 → FinMatrix R m2 m3 → FinMatrix R m1 m3
  mulFinMatrix M N i k = ∑ λ j → M i j · N j k

  ∑Exchange : ∀ {m n} → (M : FinMatrix R m n) → ∑ (λ i → ∑ (λ j → M i j)) ≡ ∑ (λ j → ∑ (λ i → M i j))
  ∑Exchange {m = zero}  {n = n}     M = sym (∑0r n)
  ∑Exchange {m = suc m} {n = zero}  M = cong (λ x → 0r + x) (∑0r m) ∙ +Rid 0r
  ∑Exchange {m = suc m} {n = suc n} M =
     let a  = M zero zero
         L  = ∑ λ j → M zero (suc j)
         C  = ∑ λ i → M (suc i) zero
         N  = ∑ λ i → ∑ λ j → M (suc i) (suc j)
         -- N reindexed
         N' = ∑ λ j → ∑ λ i → M (suc i) (suc j)
     in a + L + ∑ (λ i → ∑ (λ j → M (suc i) j)) ≡⟨ (λ k → a + L + ∑Split (λ i → M (suc i) zero) (λ i → ∑ (λ j → M (suc i) (suc j))) k) ⟩
        a + L + (C + N)                         ≡⟨ (λ k → a + L + (C + ∑Exchange (λ i j → M (suc i) (suc j)) k)) ⟩
        a + L + (C + N')                        ≡⟨ sym (+Assoc _ _ _) ⟩
        a + (L + (C + N'))                      ≡⟨ (λ k → a + +Assoc-comm1 L C N' k) ⟩
        a + (C + (L + N'))                      ≡⟨ +Assoc _ _ _ ⟩
        a + C + (L + N')                        ≡⟨ (λ k → a + C + ∑Split (λ j → M zero (suc j)) (λ j → ∑ (λ i → M (suc i) (suc j))) (~ k)) ⟩
        a + C + ∑ (λ j → ∑ (λ i → M i (suc j))) ∎


  mulFinMatrixAssoc : ∀ {m n k l} → (M : FinMatrix R m n) → (N : FinMatrix R n k) → (K : FinMatrix R k l)
                   → mulFinMatrix M (mulFinMatrix N K) ≡ mulFinMatrix (mulFinMatrix M N) K
  mulFinMatrixAssoc M N K = funExt₂ λ i j →
    ∑ (λ k → M i k · ∑ (λ l → N k l · K l j))   ≡⟨ ∑Ext (λ k → ∑Mulrdist (M i k) (λ l → N k l · K l j)) ⟩
    ∑ (λ k → ∑ (λ l → M i k · (N k l · K l j))) ≡⟨ ∑Ext (λ k → ∑Ext (λ l → ·Assoc (M i k) (N k l) (K l j))) ⟩
    ∑ (λ k → ∑ (λ l → M i k · N k l · K l j))   ≡⟨ ∑Exchange (λ k l → M i k · N k l · K l j) ⟩
    ∑ (λ l → ∑ (λ k → M i k · N k l · K l j))   ≡⟨ ∑Ext (λ l → sym (∑Mulldist (K l j) (λ k → M i k · N k l))) ⟩
    ∑ (λ l → ∑ (λ k → M i k · N k l) · K l j)   ∎

  mulFinMatrixr1 : ∀ {m n} → (M : FinMatrix R m n) → mulFinMatrix M oneFinMatrix ≡ M
  mulFinMatrixr1 M = funExt₂ λ i j → ∑Mulr1 _ (M i) j

  mulFinMatrix1r : ∀ {m n} → (M : FinMatrix R m n) → mulFinMatrix oneFinMatrix M ≡ M
  mulFinMatrix1r M = funExt₂ λ i j → ∑Mul1r _ (λ x → M x j) i

  mulFinMatrixrDistrAddFinMatrix : ∀ {n} (M N K : FinMatrix R n n)
                                 → mulFinMatrix M (addFinMatrix N K) ≡ addFinMatrix (mulFinMatrix M N) (mulFinMatrix M K)
  mulFinMatrixrDistrAddFinMatrix M N K = funExt₂ λ i j →
    ∑ (λ k → M i k · (N k j + K k j))                 ≡⟨ ∑Ext (λ k → ·Rdist+ (M i k) (N k j) (K k j)) ⟩
    ∑ (λ k → M i k · N k j + M i k · K k j)           ≡⟨ ∑Split (λ k → M i k · N k j) (λ k → M i k · K k j) ⟩
    ∑ (λ k → M i k · N k j) + ∑ (λ k → M i k · K k j) ∎

  mulFinMatrixlDistrAddFinMatrix : ∀ {n} (M N K : FinMatrix R n n)
                                 → mulFinMatrix (addFinMatrix M N) K ≡ addFinMatrix (mulFinMatrix M K) (mulFinMatrix N K)
  mulFinMatrixlDistrAddFinMatrix M N K = funExt₂ λ i j →
    ∑ (λ k → (M i k + N i k) · K k j)                 ≡⟨ ∑Ext (λ k → ·Ldist+ (M i k) (N i k) (K k j)) ⟩
    ∑ (λ k → M i k · K k j + N i k · K k j)           ≡⟨ ∑Split (λ k → M i k · K k j) (λ k → N i k · K k j) ⟩
    ∑ (λ k → M i k · K k j) + ∑ (λ k → N i k · K k j) ∎

  FinMatrixRing : (n : ℕ) → Ring ℓ
  FinMatrixRing n =
    makeRing {R = FinMatrix R n n} zeroFinMatrix oneFinMatrix addFinMatrix
             mulFinMatrix negFinMatrix isSetFinMatrix addFinMatrixAssoc
             addFinMatrix0r addFinMatrixNegMatrixr addFinMatrixComm
             mulFinMatrixAssoc mulFinMatrixr1 mulFinMatrix1r
             mulFinMatrixrDistrAddFinMatrix mulFinMatrixlDistrAddFinMatrix


-- Generators of product of two ideals

flatten : {n m : ℕ} → FinMatrix A n m → FinVec A (n ·ℕ m)
flatten {n = zero} _ ()
flatten {n = suc n} M = M zero ++Fin flatten (M ∘ suc)


flattenElim : {P : A → Type ℓ'} {n m : ℕ} (M : FinMatrix A n m)
          → (∀ i j → P (M i j))
          → (∀ i → P (flatten M i))
flattenElim {n = zero} M PMHyp ()
flattenElim {n = suc n} {m = zero} M PMHyp ind =
  ⊥.rec (¬Fin0 (transport (λ i → Fin (0≡m·0 n (~ i))) ind))
flattenElim {n = suc n} {m = suc m} M PMHyp zero = PMHyp zero zero
flattenElim {P = P} {n = suc n} {m = suc m} M PMHyp (suc i) =
  ++FinElim {P = P} (M zero ∘ suc) (flatten (M ∘ suc)) (PMHyp zero ∘ suc)
    (flattenElim {P = P} (M ∘ suc) (PMHyp ∘ suc)) i

module ProdFin (R' : CommRing ℓ) where
 private R = fst R'
 open CommRingStr (snd R') renaming ( is-set to isSetR )
 open CommRingTheory R'
 open RingTheory (CommRing→Ring R')
 open KroneckerDelta (CommRing→Ring R')
 open Sum (CommRing→Ring R')

 toMatrix : {n m : ℕ} → FinVec R n → FinVec R m → FinMatrix R n m
 toMatrix V W i j = V i · W j

 _··Fin_ : {n m : ℕ} → FinVec R n → FinVec R m → FinVec R (n ·ℕ m)
 V ··Fin W = flatten (toMatrix V W)

 ∑Dist··Fin : {n m : ℕ} (U : FinVec R n) (V : FinVec R m)
            → (∑ U) · (∑ V) ≡ ∑ (U ··Fin V)
 ∑Dist··Fin {n = zero} U V = 0LeftAnnihilates _
 ∑Dist··Fin {n = suc n} U V =
  (U zero + ∑ (U ∘ suc)) · (∑ V) ≡⟨ ·Ldist+ _ _ _ ⟩
  U zero · (∑ V) + (∑ (U ∘ suc)) · (∑ V) ≡⟨ cong₂ (_+_) (∑Mulrdist _ V) (∑Dist··Fin (U ∘ suc) V) ⟩
  ∑ (λ j → U zero · V j) + ∑ ((U ∘ suc) ··Fin V) ≡⟨ sym (∑Split++ (λ j → U zero · V j) _) ⟩
  ∑ ((λ j → U zero · V j) ++Fin ((U ∘ suc) ··Fin V)) ∎


 -- ·Dist··Fin : {n m : ℕ} (α U : FinVec R n) (β V : FinVec R m)
 --            → ∀ j → ((λ i → α i · U i) ··Fin (λ i → β i · V i)) j ≡ (α ··Fin β) j · (U ··Fin V) j
 -- ·Dist··Fin {n = n} {m = m} α U β V = equivΠ
 --   {B = λ i → (α (fst i) · U (fst i)) · (β (snd i) · V (snd i)) ≡ (α (fst i) · β (snd i)) · (U (fst i) · V (snd i))}
 --   e (equivHelper α U β V ) .fst
 --   λ _ → ·-commAssocSwap _ _ _ _
 --     where
 --     e = (FinProdChar.Equiv n m)
 --     equivHelper : {n m : ℕ} (α U : FinVec R n) (β V : FinVec R m) (a : Fin n × Fin m) →
 --        (α (fst a) · U (fst a) · (β (snd a) · V (snd a)) ≡ α (fst a) · β (snd a) · (U (fst a) · V (snd a)))
 --      ≃ (((λ i → α i · U i) ··Fin (λ i → β i · V i)) (FinProdChar.Equiv n m .fst a)
 --      ≡ (α ··Fin β) (FinProdChar.Equiv n m .fst a) · (U ··Fin V) (FinProdChar.Equiv n m .fst a))
 --     equivHelper {n = suc n} {m = suc m} α U β V (zero , zero) = idEquiv _
 --     equivHelper {n = suc n} {m = suc m} α U β V (zero , suc j) = {!!}
 --     equivHelper {n = suc n} {m = suc m} α U β V (suc i , zero) = {!!}
 --     equivHelper {n = suc n} {m = suc m} α U β V (suc i , suc j) = {!!}

 -- ·Dist··Fin {n = suc n} {m = zero} α U β V ind =
 --   ⊥.rec (¬Fin0 (transport (λ i → Fin (0≡m·0 n (~ i))) ind))
 -- ·Dist··Fin {n = suc n} {m = suc m} α U β V zero = ·-commAssocSwap _ _ _ _
 -- ·Dist··Fin {n = suc n} {m = suc m} α U β V (suc j) = {!·Dist··Fin (α ∘ suc) (U ∘ suc) β V!}
 --flattenElim (λ i j → (α i · U i) · (β j · V j)) {!!}

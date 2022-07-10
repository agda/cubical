-- define ∑ and ∏ as the bigOps of a Ring when interpreted
-- as an additive/multiplicative monoid

{-# OPTIONS --safe #-}
module Cubical.Algebra.Ring.BigOps where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Bool
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Sigma
open import Cubical.Data.FinData

open import Cubical.Algebra.Monoid.BigOp
open import Cubical.Algebra.Ring.Base
open import Cubical.Algebra.Ring.Properties

private
  variable
    ℓ ℓ' : Level

module KroneckerDelta (R' : Ring ℓ) where
 private
  R = fst R'
 open RingStr (snd R')

 δ : {n : ℕ} (i j : Fin n) → R
 δ i j = if i == j then 1r else 0r



module Sum (R' : Ring ℓ) where
 private
  R = fst R'
 open RingStr (snd R')
 open MonoidBigOp (Ring→AddMonoid R')
 open RingTheory R'
 open KroneckerDelta R'

 ∑ = bigOp
 ∑Ext = bigOpExt
 ∑0r = bigOpε
 ∑Last = bigOpLast

 ∑Split : ∀ {n} → (V W : FinVec R n) → ∑ (λ i → V i + W i) ≡ ∑ V + ∑ W
 ∑Split = bigOpSplit +Comm

 ∑Split++ : ∀ {n m : ℕ} (V : FinVec R n) (W : FinVec R m)
          → ∑ (V ++Fin W) ≡ ∑ V + ∑ W
 ∑Split++ = bigOpSplit++ +Comm

 ∑Mulrdist : ∀ {n} → (x : R) → (V : FinVec R n)
                → x · ∑ V ≡ ∑ λ i → x · V i
 ∑Mulrdist {n = zero}  x _ = 0RightAnnihilates x
 ∑Mulrdist {n = suc n} x V =
   x · (V zero + ∑ (V ∘ suc))           ≡⟨ ·DistR+ _ _ _ ⟩
   x · V zero + x · ∑ (V ∘ suc)         ≡⟨ (λ i → x · V zero + ∑Mulrdist x (V ∘ suc) i) ⟩
   x · V zero + ∑ (λ i → x · V (suc i)) ∎

 ∑Mulldist : ∀ {n} → (x : R) → (V : FinVec R n)
                → (∑ V) · x ≡ ∑ λ i → V i · x
 ∑Mulldist {n = zero}  x _ = 0LeftAnnihilates x
 ∑Mulldist {n = suc n} x V =
   (V zero + ∑ (V ∘ suc)) · x           ≡⟨ ·DistL+ _ _ _ ⟩
   V zero · x + (∑ (V ∘ suc)) · x       ≡⟨ (λ i → V zero · x + ∑Mulldist x (V ∘ suc) i) ⟩
   V zero · x + ∑ (λ i → V (suc i) · x) ∎

 ∑Mulr0 : ∀ {n} → (V : FinVec R n) → ∑ (λ i → V i · 0r) ≡ 0r
 ∑Mulr0 V = sym (∑Mulldist 0r V) ∙ 0RightAnnihilates _

 ∑Mul0r : ∀ {n} → (V : FinVec R n) → ∑ (λ i → 0r · V i) ≡ 0r
 ∑Mul0r V = sym (∑Mulrdist 0r V) ∙ 0LeftAnnihilates _

 ∑Mulr1 : (n : ℕ) (V : FinVec R n) → (j : Fin n) → ∑ (λ i → V i · δ i j) ≡ V j
 ∑Mulr1 (suc n) V zero = (λ k → ·IdR (V zero) k + ∑Mulr0 (V ∘ suc) k) ∙ +IdR (V zero)
 ∑Mulr1 (suc n) V (suc j) =
    (λ i → 0RightAnnihilates (V zero) i + ∑ (λ x → V (suc x) · δ x j))
    ∙∙ +IdL _ ∙∙ ∑Mulr1 n (V ∘ suc) j

 ∑Mul1r : (n : ℕ) (V : FinVec R n) → (j : Fin n) → ∑ (λ i → (δ j i) · V i) ≡ V j
 ∑Mul1r (suc n) V zero = (λ k → ·IdL (V zero) k + ∑Mul0r (V ∘ suc) k) ∙ +IdR (V zero)
 ∑Mul1r (suc n) V (suc j) =
   (λ i → 0LeftAnnihilates (V zero) i + ∑ (λ i → (δ j i) · V (suc i)))
   ∙∙ +IdL _ ∙∙ ∑Mul1r n (V ∘ suc) j

 ∑Dist- : ∀ {n : ℕ} (V : FinVec R n) → ∑ (λ i → - V i) ≡ - ∑ V
 ∑Dist- V = ∑Ext (λ i → -IsMult-1 (V i)) ∙ sym (∑Mulrdist _ V) ∙ sym (-IsMult-1 _)

module SumMap
  (Ar@(A , Astr) : Ring ℓ)
  (Br@(B , Bstr) : Ring ℓ')
  (f'@(f , fstr) : RingHom Ar Br)
  where

  open IsRingHom fstr

  open RingStr Astr using ()
    renaming
    ( _+_ to _+A_ )

  open RingStr Bstr using ()
    renaming
    ( _+_ to _+B_ )

  ∑Map : {n : ℕ} → (V : FinVec A n) → f (Sum.∑ Ar V) ≡ Sum.∑ Br (λ k → f (V k))
  ∑Map {n = zero} V = pres0
  ∑Map {n = suc n} V =
                       f ((V zero) +A helper) ≡⟨ pres+ (V zero) helper ⟩
                       ((f (V zero)) +B (f helper)) ≡⟨ cong (λ X → f (V zero) +B X) (∑Map (λ k → (V ∘ suc) k)) ⟩
                       Sum.∑ Br (λ k → f (V k)) ∎
                     where
                     helper : _
                     helper = foldrFin _+A_ (RingStr.0r (snd Ar)) (λ x → V (suc x))

-- anything interesting to prove here?
module Product (R' : Ring ℓ) where
 private
  R = fst R'
 open RingStr (snd R')
 open RingTheory R'
 open MonoidBigOp (Ring→MultMonoid R')

 ∏ = bigOp
 ∏Ext = bigOpExt
 ∏0r = bigOpε
 ∏Last = bigOpLast

-- only holds in CommRings!
-- ∏Split : ∀ {n} → (V W : FinVec R n) → ∏ (λ i → V i · W i) ≡ ∏ V · ∏ W
-- ∏Split = bigOpSplit MultR' ·-comm

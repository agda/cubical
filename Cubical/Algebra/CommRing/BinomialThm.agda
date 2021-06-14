{-# OPTIONS --safe #-}
module Cubical.Algebra.CommRing.BinomialThm where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Foundations.SIP
open import Cubical.Foundations.Powerset

open import Cubical.Data.Sigma
open import Cubical.Data.Nat renaming ( _+_ to _+ℕ_ ; _·_ to _·ℕ_
                                      ; ·-assoc to ·ℕ-assoc ; ·-comm to ·ℕ-comm
                                      ; _choose_ to _ℕchoose_)
open import Cubical.Data.FinData

open import Cubical.Structures.Axioms
open import Cubical.Structures.Auto
open import Cubical.Structures.Macro
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Monoid.BigOp
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Ring
open import Cubical.Algebra.Ring.BigOps
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.RingSolver.ReflectionSolving hiding (∣)

private
  variable
    ℓ : Level

module _ (R' : CommRing ℓ) where
 open CommRingStr (snd R')
 open Exponentiation R'
 open CommRingTheory R'
 open Sum (CommRing→Ring R')
 private R = fst R'

 _choose_ : ℕ → ℕ → R
 n choose zero = 1r
 zero choose suc k = 0r
 suc n choose suc k = n choose (suc k) + n choose k

 BinomialVec : (n : ℕ) → R → R → FinVec R (suc n)
 BinomialVec n x y ind = (n choose (toℕ ind)) · x ^ (toℕ ind) · y ^ (n ∸ toℕ ind)

 thm : ∀ (n : ℕ) (x y : R) → (x + y) ^ n ≡ ∑ (BinomialVec n x y)
 thm zero x y = solve R'
 thm (suc n) x y =
     (x + y) ^ suc n
  ≡⟨ refl ⟩
     (x + y) · (x + y) ^ n
  ≡⟨ cong ((x + y) ·_) (thm n x y) ⟩
     (x + y) · ∑ (BinomialVec n x y)
  ≡⟨ ·Ldist+ _ _ _ ⟩
     x · ∑ (BinomialVec n x y) + y · ∑ (BinomialVec n x y)
  ≡⟨ cong₂ (_+_) (∑Mulrdist _ (BinomialVec n x y)) (∑Mulrdist _ (BinomialVec n x y)) ⟩
     ∑ (λ i → x · BinomialVec n x y i)
   + ∑ (λ i → y · BinomialVec n x y i)
  ≡⟨ refl ⟩
     ∑ {n = suc n} (λ i → x · ((n choose (toℕ i)) · x ^ (toℕ i) · y ^ (n ∸ toℕ i)))
   + ∑ {n = suc n} (λ i → y · ((n choose (toℕ i)) · x ^ (toℕ i) · y ^ (n ∸ toℕ i)))
  ≡⟨ {!!} ⟩
{-
first sum ≡ xⁿ⁺¹ (top element)
          + ∑ λ i → (n choose (toℕ toSuc i)) · x ^ (suc toℕ toSuc i) · y ^ (n ∸ toℕ toSuc i)
need lemma:
∑ {suc n} V ≡ V topEl + ∑ {n} λ i → V (toSuc i)

where toSuc : Fin n → Fin (suc n) id-embedding
then toℕ {n} ∘ toSuc ≡ toℕ {suc n}
and we can ignore the toSuc part...

the top element topEl : Fin (suc n) is given by (fromℕ n)
have weakenFin and weakenRespToℕ now
lemma is called ∑Top

second sum ≡ yⁿ⁺¹ (zero el ≡ (n choose 0) · x ^ 0 · y ^ (suc n ∸ toℕ zero))
           + ∑ λ i → (n choose (toℕ suc i)) · x ^ (toℕ suc i) · y ^ (suc n ∸ toℕ suc i)
no need for lemma as
 bigOpLeftRes : ∀ {n} (V : FinVec M (suc n)) → bigOp V ≡ V zero · bigOp (V ∘ suc)
 bigOpLeftRes V = refl
for any monoid M

using split
... ≡ xⁿ⁺¹ + yⁿ⁺¹
    + ∑ λ i → ((n choose toℕ i) + (n choose suc toℕ i)) · x ^ (toℕ suc i) · y ^ (suc n ∸ toℕ suc i)
              ≡ (suc n choose toℕ suc i) by refl!!!
... ≡ xⁿ⁺¹
    + ∑ λ i → (suc n choose toℕ i) · x ^ (toℕ i) · y ^ (suc n ∸ toℕ i)
-}
     ∑ (BinomialVec (suc n) x y) ∎

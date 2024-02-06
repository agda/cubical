{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Algebra.CommRing.BinomialThm where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat renaming ( _+_ to _+ℕ_ ; _·_ to _·ℕ_ ; _^_ to _^ℕ_
                                      ; +-comm to +ℕ-comm
                                      ; ·-assoc to ·ℕ-assoc ; ·-comm to ·ℕ-comm
                                      ; _choose_ to _ℕchoose_ ; snotz to ℕsnotz)
open import Cubical.Data.Nat.Order
open import Cubical.Data.FinData
open import Cubical.Data.Empty as ⊥

open import Cubical.Algebra.Monoid.BigOp
open import Cubical.Algebra.Ring.BigOps
open import Cubical.Algebra.CommRing
open import Cubical.Tactics.CommRingSolver

private
  variable
    ℓ : Level

module BinomialThm (R' : CommRing ℓ) where
 open CommRingStr (snd R')
 open Exponentiation R'
 open CommRingTheory R'
 open Sum (CommRing→Ring R')
 private R = fst R'

 _choose_ : ℕ → ℕ → R
 n choose zero = 1r
 zero choose suc k = 0r
 suc n choose suc k = n choose (suc k) + n choose k

 n<k→nChooseK≡0 : ∀ n k → n < k → n choose k ≡ 0r
 n<k→nChooseK≡0 zero zero (m , p) = ⊥.rec (ℕsnotz (sym (+ℕ-comm m 1) ∙ p))
 n<k→nChooseK≡0 zero (suc k) (m , p) = refl
 n<k→nChooseK≡0 (suc n) zero (m , p) = ⊥.rec (ℕsnotz {n = m +ℕ (suc n)} (sym (+-suc _ _) ∙ p))
 n<k→nChooseK≡0 (suc n) (suc k) (m , p) = cong₂ (_+_) p1 p2 ∙ +IdL 0r
  where
  p1 : n choose suc k ≡ 0r
  p1 = n<k→nChooseK≡0 n (suc k) (suc m , sym (+-suc _ _) ∙ p)
  p2 : n choose k ≡ 0r
  p2 =  n<k→nChooseK≡0 n k (m , injSuc (sym (+-suc _ _) ∙ p))

 nChooseN+1 : ∀ n → n choose (suc n) ≡ 0r
 nChooseN+1 n = n<k→nChooseK≡0 n (suc n) (0 , refl)

 BinomialVec : (n : ℕ) → R → R → FinVec R (suc n)
 BinomialVec n x y i = (n choose (toℕ i)) · x ^ (toℕ i) · y ^ (n ∸ toℕ i)

 BinomialThm : ∀ (n : ℕ) (x y : R) → (x + y) ^ n ≡ ∑ (BinomialVec n x y)
 BinomialThm zero x y = solve! R'
 BinomialThm (suc n) x y =
     (x + y) ^ suc n
  ≡⟨ refl ⟩
     (x + y) · (x + y) ^ n
  ≡⟨ cong ((x + y) ·_) (BinomialThm n x y) ⟩
     (x + y) · ∑ (BinomialVec n x y)
  ≡⟨ ·DistL+ _ _ _ ⟩
     x · ∑ (BinomialVec n x y) + y · ∑ (BinomialVec n x y)
  ≡⟨ cong₂ (_+_) (∑Mulrdist _ (BinomialVec n x y)) (∑Mulrdist _ (BinomialVec n x y)) ⟩
     ∑ (λ i → x · BinomialVec n x y i)
   + ∑ (λ i → y · BinomialVec n x y i)
  ≡⟨ refl ⟩
     ∑ {n = suc n} (λ i → x · ((n choose (toℕ i)) · x ^ (toℕ i) · y ^ (n ∸ toℕ i)))
   + ∑ {n = suc n} (λ i → y · ((n choose (toℕ i)) · x ^ (toℕ i) · y ^ (n ∸ toℕ i)))
  ≡⟨ cong₂ (_+_) (∑Ext xVecPath) (∑Ext yVecPath) ⟩
     ∑ xVec + ∑ yVec
  ≡⟨ cong (_+ ∑ yVec) (∑Last xVec) ⟩
     ∑ (xVec ∘ weakenFin) + xⁿ⁺¹ + (yⁿ⁺¹ + ∑ (yVec ∘ suc))
  ≡⟨  solve3 _ _ _ _ ⟩
     yⁿ⁺¹  + (∑ (xVec ∘ weakenFin) + ∑ (yVec ∘ suc)) + xⁿ⁺¹
  ≡⟨ cong (λ s → yⁿ⁺¹  + s + xⁿ⁺¹) (sym (∑Split _ _))  ⟩
     yⁿ⁺¹  + (∑ middleVec) + xⁿ⁺¹
  ≡⟨ cong (λ s → yⁿ⁺¹  + s + xⁿ⁺¹) (∑Ext middlePath) ⟩
     yⁿ⁺¹ + ∑ ((BinomialVec (suc n) x y) ∘ weakenFin ∘ suc) + xⁿ⁺¹
  ≡⟨ refl ⟩
     ∑ ((BinomialVec (suc n) x y) ∘ weakenFin) + xⁿ⁺¹
  ≡⟨ cong (∑ ((BinomialVec (suc n) x y) ∘ weakenFin) +_) xⁿ⁺¹Path
   ∙ sym (∑Last (BinomialVec (suc n) x y)) ⟩
     ∑ (BinomialVec (suc n) x y) ∎
  where
  xVec : FinVec R (suc n)
  xVec i = (n choose (toℕ i)) · x ^ (suc (toℕ i)) · y ^ (n ∸ toℕ i)

  xVecPath : ∀ (i : Fin (suc n)) → x · ((n choose (toℕ i)) · x ^ (toℕ i) · y ^ (n ∸ toℕ i)) ≡ xVec i
  xVecPath i = solve! R'

  yVec : FinVec R (suc n)
  yVec i = (n choose (toℕ i)) · x ^ (toℕ i) · y ^ (suc (n ∸ toℕ i))

  yVecPath : ∀ (i : Fin (suc n)) → y · ((n choose (toℕ i)) · x ^ (toℕ i) · y ^ (n ∸ toℕ i)) ≡ yVec i
  yVecPath i = solve! R'

  xⁿ⁺¹ : R
  xⁿ⁺¹ = xVec (fromℕ n)
  yⁿ⁺¹ : R
  yⁿ⁺¹ = yVec zero

  xⁿ⁺¹Path : xⁿ⁺¹ ≡ BinomialVec (suc n) x y (fromℕ (suc n))
  xⁿ⁺¹Path = cong (λ m → m · (x · x ^ toℕ (fromℕ n)) · y ^ (n ∸ toℕ (fromℕ n)))
                  (sym (+IdL _) ∙ cong (_+ (n choose toℕ (fromℕ n)))
                  (sym (subst (λ m → (n choose suc m) ≡ 0r) (sym (toFromId n)) (nChooseN+1 n))))

  solve3 : ∀ sx sy xⁿ⁺¹ yⁿ⁺¹ → sx + xⁿ⁺¹ + (yⁿ⁺¹ + sy) ≡ yⁿ⁺¹ + (sx + sy) + xⁿ⁺¹
  solve3 sx sy xⁿ⁺¹ yⁿ⁺¹ = solve! R'

  middleVec : FinVec R n
  middleVec i = xVec (weakenFin i) + yVec (suc i)

  middlePath : ∀ (i : Fin n) → middleVec i ≡ BinomialVec (suc n) x y (weakenFin (suc i))
  middlePath i = transport (λ j →
     (n choose toℕ (weakenFin i)) · (x · x ^ toℕ (weakenFin i)) · y ^ (n ∸ toℕ (weakenFin i))
   + (n choose suc (weakenRespToℕ i j)) · (x · x ^ (weakenRespToℕ i j)) · sym yHelper j
   ≡ ((n choose suc (toℕ (weakenFin i))) + (n choose toℕ (weakenFin i)))
   · (x · x ^ toℕ (weakenFin i)) · y ^ (n ∸ toℕ (weakenFin i)))
   (solve! R')
   where
   yHelper : (y · y ^ (n ∸ suc (toℕ i))) ≡ y ^ (n ∸ toℕ (weakenFin i))
   yHelper = cong (λ m → y · y ^ (n ∸ suc m)) (sym (weakenRespToℕ i))
           ∙ cong (y ^_) (≤-∸-suc (subst (λ m → suc m ≤ n) (sym (weakenRespToℕ _)) (toℕ<n i)))

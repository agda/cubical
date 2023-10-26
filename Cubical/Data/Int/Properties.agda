{-# OPTIONS --safe #-}
module Cubical.Data.Int.Properties where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

open import Cubical.Relation.Nullary

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Bool
open import Cubical.Data.Nat
  hiding   (+-assoc ; +-comm ; min ; max ; minComm ; maxComm)
  renaming (_·_ to _·ℕ_; _+_ to _+ℕ_ ; ·-assoc to ·ℕ-assoc ;
            ·-comm to ·ℕ-comm ; isEven to isEvenℕ ; isOdd to isOddℕ)
open import Cubical.Data.Sum

open import Cubical.Data.Int.Base

min : ℤ → ℤ → ℤ
min (pos zero) (pos m) = pos zero
min (pos (suc n)) (pos zero) = pos zero
min (pos (suc n)) (pos (suc m)) = sucℤ (min (pos n) (pos m))
min (negsuc n) (pos m) = negsuc n
min (pos n) (negsuc m) = negsuc m
min (negsuc zero) (negsuc m) = negsuc m
min (negsuc (suc n)) (negsuc zero) = negsuc (suc n)
min (negsuc (suc n)) (negsuc (suc m)) = predℤ (min (negsuc n) (negsuc m))

minComm : ∀ n m → min n m ≡ min m n
minComm (pos zero) (pos zero) = refl
minComm (pos zero) (pos (suc m)) = refl
minComm (pos (suc n)) (pos zero) = refl
minComm (pos (suc n)) (pos (suc m)) = cong sucℤ (minComm (pos n) (pos m))
minComm (pos zero) (negsuc zero) = refl
minComm (pos zero) (negsuc (suc m)) = refl
minComm (pos (suc n)) (negsuc zero) = refl
minComm (pos (suc n)) (negsuc (suc m)) = refl
minComm (negsuc zero) (pos zero) = refl
minComm (negsuc zero) (pos (suc m)) = refl
minComm (negsuc (suc n)) (pos zero) = refl
minComm (negsuc (suc n)) (pos (suc m)) = refl
minComm (negsuc zero) (negsuc zero) = refl
minComm (negsuc zero) (negsuc (suc m)) = refl
minComm (negsuc (suc n)) (negsuc zero) = refl
minComm (negsuc (suc n)) (negsuc (suc m)) = cong predℤ (minComm (negsuc n) (negsuc m))

minIdem : ∀ n → min n n ≡ n
minIdem (pos zero) = refl
minIdem (pos (suc n)) = cong sucℤ (minIdem (pos n))
minIdem (negsuc zero) = refl
minIdem (negsuc (suc n)) = cong predℤ (minIdem (negsuc n))

max : ℤ → ℤ → ℤ
max (pos zero) (pos m) = pos m
max (pos (suc n)) (pos zero) = pos (suc n)
max (pos (suc n)) (pos (suc m)) = sucℤ (max (pos n) (pos m))
max (pos n) (negsuc m) = pos n
max (negsuc n) (pos m) = pos m
max (negsuc zero) (negsuc m) = negsuc zero
max (negsuc (suc n)) (negsuc zero) = negsuc zero
max (negsuc (suc n)) (negsuc (suc m)) = predℤ (max (negsuc n) (negsuc m))

maxComm : ∀ n m → max n m ≡ max m n
maxComm (pos zero) (pos zero) = refl
maxComm (pos zero) (pos (suc m)) = refl
maxComm (pos (suc n)) (pos zero) = refl
maxComm (pos (suc n)) (pos (suc m)) = cong sucℤ (maxComm (pos n) (pos m))
maxComm (pos zero) (negsuc zero) = refl
maxComm (pos zero) (negsuc (suc m)) = refl
maxComm (pos (suc n)) (negsuc zero) = refl
maxComm (pos (suc n)) (negsuc (suc m)) = refl
maxComm (negsuc zero) (pos zero) = refl
maxComm (negsuc zero) (pos (suc m)) = refl
maxComm (negsuc (suc n)) (pos zero) = refl
maxComm (negsuc (suc n)) (pos (suc m)) = refl
maxComm (negsuc zero) (negsuc zero) = refl
maxComm (negsuc zero) (negsuc (suc m)) = refl
maxComm (negsuc (suc n)) (negsuc zero) = refl
maxComm (negsuc (suc n)) (negsuc (suc m)) = cong predℤ (maxComm (negsuc n) (negsuc m))

maxIdem : ∀ n → max n n ≡ n
maxIdem (pos zero) = refl
maxIdem (pos (suc n)) = cong sucℤ (maxIdem (pos n))
maxIdem (negsuc zero) = refl
maxIdem (negsuc (suc n)) = cong predℤ (maxIdem (negsuc n))

sucPred : ∀ i → sucℤ (predℤ i) ≡ i
sucPred (pos zero)    = refl
sucPred (pos (suc n)) = refl
sucPred (negsuc n)    = refl

predSuc : ∀ i → predℤ (sucℤ i) ≡ i
predSuc (pos n)          = refl
predSuc (negsuc zero)    = refl
predSuc (negsuc (suc n)) = refl

sucDistMin : ∀ m n → sucℤ (min m n) ≡ min (sucℤ m) (sucℤ n)
sucDistMin (pos zero) (pos zero) = refl
sucDistMin (pos zero) (pos (suc n)) = refl
sucDistMin (pos (suc m)) (pos zero) = refl
sucDistMin (pos (suc m)) (pos (suc n)) = refl
sucDistMin (pos zero) (negsuc zero) = refl
sucDistMin (pos zero) (negsuc (suc n)) = refl
sucDistMin (pos (suc m)) (negsuc zero) = refl
sucDistMin (pos (suc m)) (negsuc (suc n)) = refl
sucDistMin (negsuc zero) (pos zero) = refl
sucDistMin (negsuc zero) (pos (suc n)) = refl
sucDistMin (negsuc (suc m)) (pos zero) = refl
sucDistMin (negsuc (suc m)) (pos (suc n)) = refl
sucDistMin (negsuc zero) (negsuc zero) = refl
sucDistMin (negsuc zero) (negsuc (suc n)) = refl
sucDistMin (negsuc (suc m)) (negsuc zero) = refl
sucDistMin (negsuc (suc m)) (negsuc (suc n)) = sucPred _

predDistMin : ∀ m n → predℤ (min m n) ≡ min (predℤ m) (predℤ n)
predDistMin (pos zero) (pos zero) = refl
predDistMin (pos zero) (pos (suc n)) = refl
predDistMin (pos (suc m)) (pos zero) = minComm (negsuc zero) (pos m)
predDistMin (pos (suc m)) (pos (suc n)) = predSuc _
predDistMin (pos zero) (negsuc zero) = refl
predDistMin (pos zero) (negsuc (suc n)) = refl
predDistMin (pos (suc m)) (negsuc zero) = minComm (negsuc 1) (pos m)
predDistMin (pos (suc m)) (negsuc (suc n)) = minComm (negsuc (suc (suc n))) (pos m)
predDistMin (negsuc zero) (pos zero) = refl
predDistMin (negsuc zero) (pos (suc n)) = refl
predDistMin (negsuc (suc m)) (pos zero) = refl
predDistMin (negsuc (suc m)) (pos (suc n)) = refl
predDistMin (negsuc zero) (negsuc zero) = refl
predDistMin (negsuc zero) (negsuc (suc n)) = refl
predDistMin (negsuc (suc m)) (negsuc zero) = refl
predDistMin (negsuc (suc m)) (negsuc (suc n)) = refl

minSucL : ∀ m → min (sucℤ m) m ≡ m
minSucL (pos zero) = refl
minSucL (pos (suc m)) = cong sucℤ (minSucL (pos m))
minSucL (negsuc zero) = refl
minSucL (negsuc (suc m))
  = sym (cong predℤ (sym (minSucL (negsuc m))) ∙
         predDistMin (sucℤ (negsuc m)) (negsuc m) ∙
         cong (λ a → min a (negsuc (suc m))) (predSuc (negsuc m)))

minSucR : ∀ m → min m (sucℤ m) ≡ m
minSucR m = minComm m (sucℤ m) ∙ minSucL m

minPredL : ∀ m → min (predℤ m) m ≡ predℤ m
minPredL (pos zero) = refl
minPredL (pos (suc m)) = minSucR (pos m)
minPredL (negsuc zero) = refl
minPredL (negsuc (suc m)) = cong predℤ (minPredL (negsuc m))

minPredR : ∀ m → min m (predℤ m) ≡ predℤ m
minPredR m = minComm m (predℤ m) ∙ minPredL m

sucDistMax : ∀ m n → sucℤ (max m n) ≡ max (sucℤ m) (sucℤ n)
sucDistMax (pos zero) (pos zero) = refl
sucDistMax (pos zero) (pos (suc n)) = refl
sucDistMax (pos (suc m)) (pos zero) = refl
sucDistMax (pos (suc m)) (pos (suc n)) = refl
sucDistMax (pos zero) (negsuc zero) = refl
sucDistMax (pos zero) (negsuc (suc n)) = refl
sucDistMax (pos (suc m)) (negsuc zero) = refl
sucDistMax (pos (suc m)) (negsuc (suc n)) = refl
sucDistMax (negsuc zero) (pos zero) = refl
sucDistMax (negsuc zero) (pos (suc n)) = refl
sucDistMax (negsuc (suc m)) (pos zero) = refl
sucDistMax (negsuc (suc m)) (pos (suc n)) = refl
sucDistMax (negsuc zero) (negsuc zero) = refl
sucDistMax (negsuc zero) (negsuc (suc n)) = refl
sucDistMax (negsuc (suc m)) (negsuc zero) = refl
sucDistMax (negsuc (suc m)) (negsuc (suc n)) = sucPred _

predDistMax : ∀ m n → predℤ (max m n) ≡ max (predℤ m) (predℤ n)
predDistMax (pos zero) (pos zero) = refl
predDistMax (pos zero) (pos (suc n)) = refl
predDistMax (pos (suc m)) (pos zero) = maxComm (negsuc zero) (pos m)
predDistMax (pos (suc m)) (pos (suc n)) = predSuc _
predDistMax (pos zero) (negsuc zero) = refl
predDistMax (pos zero) (negsuc (suc n)) = refl
predDistMax (pos (suc m)) (negsuc zero) = maxComm (negsuc 1) (pos m)
predDistMax (pos (suc m)) (negsuc (suc n)) = maxComm (negsuc (suc (suc n))) (pos m)
predDistMax (negsuc zero) (pos zero) = refl
predDistMax (negsuc zero) (pos (suc n)) = refl
predDistMax (negsuc (suc m)) (pos zero) = refl
predDistMax (negsuc (suc m)) (pos (suc n)) = refl
predDistMax (negsuc zero) (negsuc zero) = refl
predDistMax (negsuc zero) (negsuc (suc n)) = refl
predDistMax (negsuc (suc m)) (negsuc zero) = refl
predDistMax (negsuc (suc m)) (negsuc (suc n)) = refl

maxSucL : ∀ m → max (sucℤ m) m ≡ sucℤ m
maxSucL (pos zero) = refl
maxSucL (pos (suc m)) = cong sucℤ (maxSucL (pos m))
maxSucL (negsuc zero) = refl
maxSucL (negsuc (suc m))
  = cong (λ a → max a (negsuc (suc m))) (sym (predSuc (negsuc m))) ∙
    sym (predDistMax (sucℤ (negsuc m)) (negsuc m)) ∙
    cong predℤ (maxSucL (negsuc m)) ∙
    predSuc (negsuc m)

maxSucR : ∀ m → max m (sucℤ m) ≡ sucℤ m
maxSucR m = maxComm m (sucℤ m) ∙ maxSucL m

maxPredL : ∀ m → max (predℤ m) m ≡ m
maxPredL (pos zero) = refl
maxPredL (pos (suc m)) = maxSucR (pos m)
maxPredL (negsuc zero) = refl
maxPredL (negsuc (suc m)) = cong predℤ (maxPredL (negsuc m))

maxPredR : ∀ m → max m (predℤ m) ≡ m
maxPredR m = maxComm m (predℤ m) ∙ maxPredL m

minAssoc : ∀ x y z → min x (min y z) ≡ min (min x y) z
minAssoc (pos zero) (pos zero) (pos z) = refl
minAssoc (pos zero) (pos (suc y)) (pos zero) = refl
minAssoc (pos zero) (pos (suc y)) (pos (suc z))
  = sym (sucDistMin (negsuc zero) (min (pos y) (pos z))) ∙
    cong sucℤ (minAssoc (negsuc zero) (pos y) (pos z))
minAssoc (pos (suc x)) (pos zero) (pos z) = refl
minAssoc (pos (suc x)) (pos (suc y)) (pos zero)
  = cong (min (pos (suc x))) (sym (sucDistMin (pos y) (negsuc zero))) ∙
    sym (sucDistMin (pos x) (min (pos y) (negsuc zero))) ∙
    cong sucℤ (minAssoc (pos x) (pos y) (negsuc zero)) ∙
    sucDistMin (min (pos x) (pos y)) (negsuc zero)
minAssoc (pos (suc x)) (pos (suc y)) (pos (suc z))
  = sym (sucDistMin (pos x) (min (pos y) (pos z))) ∙
    cong sucℤ (minAssoc (pos x) (pos y) (pos z)) ∙
    sucDistMin (min (pos x) (pos y)) (pos z)
minAssoc (pos zero) (pos zero) (negsuc z) = refl
minAssoc (pos zero) (pos (suc y)) (negsuc z) = refl
minAssoc (pos (suc x)) (pos zero) (negsuc z) = refl
minAssoc (pos (suc x)) (pos (suc y)) (negsuc z)
  = cong (min (pos (suc x))) (sym (sucDistMin (pos y) (negsuc (suc z)))) ∙
    sym (sucDistMin (pos x) (min (pos y) (negsuc (suc z)))) ∙
    cong sucℤ (minAssoc (pos x) (pos y) (negsuc (suc z))) ∙
    sucDistMin (min (pos x) (pos y)) (negsuc (suc z))
minAssoc (pos zero) (negsuc y) (pos z) = refl
minAssoc (pos (suc x)) (negsuc y) (pos z) = refl
minAssoc (pos zero) (negsuc zero) (negsuc z) = refl
minAssoc (pos zero) (negsuc (suc y)) (negsuc zero) = refl
minAssoc (pos zero) (negsuc (suc y)) (negsuc (suc z))
  = sym (predDistMin (pos 1) (min (negsuc y) (negsuc z))) ∙
    cong predℤ (minAssoc (pos 1) (negsuc y) (negsuc z)) ∙
    predDistMin (min (pos 1) (negsuc y)) (negsuc z)
minAssoc (pos (suc x)) (negsuc zero) (negsuc z) = refl
minAssoc (pos (suc x)) (negsuc (suc y)) (negsuc zero) = refl
minAssoc (pos (suc x)) (negsuc (suc y)) (negsuc (suc z))
  = sym (predDistMin (pos (suc (suc x))) (min (negsuc y) (negsuc z))) ∙
    cong predℤ (minAssoc (pos (suc (suc x))) (negsuc y) (negsuc z)) ∙
    predDistMin (min (pos (suc (suc x))) (negsuc y)) (negsuc z)
minAssoc (negsuc x) (pos zero) (pos z) = refl
minAssoc (negsuc x) (pos (suc y)) (pos zero) = refl
minAssoc (negsuc zero) (pos (suc y)) (pos (suc z))
  = sym (sucDistMin (negsuc 1) (min (pos y) (pos z))) ∙
    cong sucℤ (minAssoc (negsuc 1) (pos y) (pos z)) ∙
    sucDistMin (min (negsuc 1) (pos y)) (pos z)
minAssoc (negsuc (suc x)) (pos (suc y)) (pos (suc z))
  = sym (sucDistMin (negsuc (suc (suc x))) (min (pos y) (pos z))) ∙
    cong sucℤ (minAssoc (negsuc (suc (suc x))) (pos y) (pos z))
minAssoc (negsuc x) (pos zero) (negsuc z) = refl
minAssoc (negsuc x) (pos (suc y)) (negsuc z) = refl
minAssoc (negsuc zero) (negsuc y) (pos z) = refl
minAssoc (negsuc (suc x)) (negsuc zero) (pos z) = refl
minAssoc (negsuc (suc x)) (negsuc (suc y)) (pos z)
  = cong predℤ (minAssoc (negsuc x) (negsuc y) (pos (suc z))) ∙
    predDistMin (min (negsuc x) (negsuc y)) (pos (suc z))
minAssoc (negsuc zero) (negsuc zero) (negsuc z) = refl
minAssoc (negsuc zero) (negsuc (suc y)) (negsuc zero) = refl
minAssoc (negsuc zero) (negsuc (suc y)) (negsuc (suc z))
  = sym (predDistMin (pos zero) (min (negsuc y) (negsuc z))) ∙
    cong predℤ (minAssoc (pos zero) (negsuc y) (negsuc z))
minAssoc (negsuc (suc x)) (negsuc zero) (negsuc z) = refl
minAssoc (negsuc (suc x)) (negsuc (suc y)) (negsuc zero)
  = cong predℤ (minAssoc (negsuc x) (negsuc y) (pos zero)) ∙
    predDistMin (min (negsuc x) (negsuc y)) (pos zero)
minAssoc (negsuc (suc x)) (negsuc (suc y)) (negsuc (suc z))
  = sym (predDistMin (negsuc x) (min (negsuc y) (negsuc z))) ∙
    cong predℤ (minAssoc (negsuc x) (negsuc y) (negsuc z)) ∙
    predDistMin (min (negsuc x) (negsuc y)) (negsuc z)

maxAssoc : ∀ x y z → max x (max y z) ≡ max (max x y) z
maxAssoc (pos zero) (pos zero) (pos z) = refl
maxAssoc (pos zero) (pos (suc y)) (pos zero) = refl
maxAssoc (pos zero) (pos (suc y)) (pos (suc z))
  = sym (sucDistMax (negsuc zero) (max (pos y) (pos z))) ∙
    cong sucℤ (maxAssoc (negsuc zero) (pos y) (pos z))
maxAssoc (pos (suc x)) (pos zero) (pos z) = refl
maxAssoc (pos (suc x)) (pos (suc y)) (pos zero)
  = cong (max (pos (suc x))) (sym (sucDistMax (pos y) (negsuc zero))) ∙
    sym (sucDistMax (pos x) (max (pos y) (negsuc zero))) ∙
    cong sucℤ (maxAssoc (pos x) (pos y) (negsuc zero)) ∙
    sucDistMax (max (pos x) (pos y)) (negsuc zero)
maxAssoc (pos (suc x)) (pos (suc y)) (pos (suc z))
  = sym (sucDistMax (pos x) (max (pos y) (pos z))) ∙
    cong sucℤ (maxAssoc (pos x) (pos y) (pos z)) ∙
    sucDistMax (max (pos x) (pos y)) (pos z)
maxAssoc (pos zero) (pos zero) (negsuc z) = refl
maxAssoc (pos zero) (pos (suc y)) (negsuc z) = refl
maxAssoc (pos (suc x)) (pos zero) (negsuc z) = refl
maxAssoc (pos (suc x)) (pos (suc y)) (negsuc z)
  = cong (max (pos (suc x))) (sym (sucDistMax (pos y) (negsuc (suc z)))) ∙
    sym (sucDistMax (pos x) (max (pos y) (negsuc (suc z)))) ∙
    cong sucℤ (maxAssoc (pos x) (pos y) (negsuc (suc z))) ∙
    sucDistMax (max (pos x) (pos y)) (negsuc (suc z))
maxAssoc (pos zero) (negsuc y) (pos z) = refl
maxAssoc (pos (suc x)) (negsuc y) (pos z) = refl
maxAssoc (pos zero) (negsuc zero) (negsuc z) = refl
maxAssoc (pos zero) (negsuc (suc y)) (negsuc zero) = refl
maxAssoc (pos zero) (negsuc (suc y)) (negsuc (suc z))
  = sym (predDistMax (pos 1) (max (negsuc y) (negsuc z))) ∙
    cong predℤ (maxAssoc (pos 1) (negsuc y) (negsuc z)) ∙
    predDistMax (max (pos 1) (negsuc y)) (negsuc z)
maxAssoc (pos (suc x)) (negsuc zero) (negsuc z) = refl
maxAssoc (pos (suc x)) (negsuc (suc y)) (negsuc zero) = refl
maxAssoc (pos (suc x)) (negsuc (suc y)) (negsuc (suc z))
  = sym (predDistMax (pos (suc (suc x))) (max (negsuc y) (negsuc z))) ∙
    cong predℤ (maxAssoc (pos (suc (suc x))) (negsuc y) (negsuc z)) ∙
    predDistMax (max (pos (suc (suc x))) (negsuc y)) (negsuc z)
maxAssoc (negsuc x) (pos zero) (pos z) = refl
maxAssoc (negsuc x) (pos (suc y)) (pos zero) = refl
maxAssoc (negsuc zero) (pos (suc y)) (pos (suc z))
  = sym (sucDistMax (negsuc 1) (max (pos y) (pos z))) ∙
    cong sucℤ (maxAssoc (negsuc 1) (pos y) (pos z)) ∙
    sucDistMax (max (negsuc 1) (pos y)) (pos z)
maxAssoc (negsuc (suc x)) (pos (suc y)) (pos (suc z))
  = sym (sucDistMax (negsuc (suc (suc x))) (max (pos y) (pos z))) ∙
    cong sucℤ (maxAssoc (negsuc (suc (suc x))) (pos y) (pos z))
maxAssoc (negsuc x) (pos zero) (negsuc z) = refl
maxAssoc (negsuc x) (pos (suc y)) (negsuc z) = refl
maxAssoc (negsuc zero) (negsuc y) (pos z) = refl
maxAssoc (negsuc (suc x)) (negsuc zero) (pos z) = refl
maxAssoc (negsuc (suc x)) (negsuc (suc y)) (pos z)
  = cong predℤ (maxAssoc (negsuc x) (negsuc y) (pos (suc z))) ∙
    predDistMax (max (negsuc x) (negsuc y)) (pos (suc z))
maxAssoc (negsuc zero) (negsuc zero) (negsuc z) = refl
maxAssoc (negsuc zero) (negsuc (suc y)) (negsuc zero) = refl
maxAssoc (negsuc zero) (negsuc (suc y)) (negsuc (suc z))
  = sym (predDistMax (pos zero) (max (negsuc y) (negsuc z))) ∙
    cong predℤ (maxAssoc (pos zero) (negsuc y) (negsuc z))
maxAssoc (negsuc (suc x)) (negsuc zero) (negsuc z) = refl
maxAssoc (negsuc (suc x)) (negsuc (suc y)) (negsuc zero)
  = cong predℤ (maxAssoc (negsuc x) (negsuc y) (pos zero)) ∙
    predDistMax (max (negsuc x) (negsuc y)) (pos zero)
maxAssoc (negsuc (suc x)) (negsuc (suc y)) (negsuc (suc z))
  = sym (predDistMax (negsuc x) (max (negsuc y) (negsuc z))) ∙
    cong predℤ (maxAssoc (negsuc x) (negsuc y) (negsuc z)) ∙
    predDistMax (max (negsuc x) (negsuc y)) (negsuc z)

minAbsorbLMax : ∀ x y → min x (max x y) ≡ x
minAbsorbLMax (pos zero) (pos y) = refl
minAbsorbLMax (pos (suc x)) (pos zero) = cong sucℤ (minIdem (pos x))
minAbsorbLMax (pos (suc x)) (pos (suc y))
  = sym (sucDistMin (pos x) (max (pos x) (pos y))) ∙
    cong sucℤ (minAbsorbLMax (pos x) (pos y))
minAbsorbLMax (pos zero) (negsuc zero) = refl
minAbsorbLMax (pos zero) (negsuc (suc y)) = refl
minAbsorbLMax (pos (suc x)) (negsuc y) = cong sucℤ (minIdem (pos x))
minAbsorbLMax (negsuc x) (pos y) = refl
minAbsorbLMax (negsuc zero) (negsuc y) = refl
minAbsorbLMax (negsuc (suc x)) (negsuc zero) = refl
minAbsorbLMax (negsuc (suc x)) (negsuc (suc y))
  = sym (predDistMin (negsuc x) (max (negsuc x) (negsuc y))) ∙
    cong predℤ (minAbsorbLMax (negsuc x) (negsuc y))

maxAbsorbLMin : ∀ x y → max x (min x y) ≡ x
maxAbsorbLMin (pos zero) (pos y) = refl
maxAbsorbLMin (pos (suc x)) (pos zero) = refl
maxAbsorbLMin (pos (suc x)) (pos (suc y))
  = sym (sucDistMax (pos x) (min (pos x) (pos y))) ∙
    cong sucℤ (maxAbsorbLMin (pos x) (pos y))
maxAbsorbLMin (pos zero) (negsuc y) = refl
maxAbsorbLMin (pos (suc x)) (negsuc y) = refl
maxAbsorbLMin (negsuc x) (pos y) = maxIdem (negsuc x)
maxAbsorbLMin (negsuc zero) (negsuc y) = refl
maxAbsorbLMin (negsuc (suc x)) (negsuc zero) = maxIdem (negsuc (suc x))
maxAbsorbLMin (negsuc (suc x)) (negsuc (suc y))
  = sym (predDistMax (negsuc x) (min (negsuc x) (negsuc y))) ∙
    cong predℤ (maxAbsorbLMin (negsuc x) (negsuc y))

injPos : ∀ {a b : ℕ} → pos a ≡ pos b → a ≡ b
injPos {a} h = subst T h refl
  where
  T : ℤ → Type₀
  T (pos x)    = a ≡ x
  T (negsuc _) = ⊥

injNegsuc : ∀ {a b : ℕ} → negsuc a ≡ negsuc b → a ≡ b
injNegsuc {a} h = subst T h refl
  where
  T : ℤ → Type₀
  T (pos _) = ⊥
  T (negsuc x) = a ≡ x

posNotnegsuc : ∀ (a b : ℕ) → ¬ (pos a ≡ negsuc b)
posNotnegsuc a b h = subst T h 0
  where
  T : ℤ → Type₀
  T (pos _)    = ℕ
  T (negsuc _) = ⊥

negsucNotpos : ∀ (a b : ℕ) → ¬ (negsuc a ≡ pos b)
negsucNotpos a b h = subst T h 0
  where
  T : ℤ → Type₀
  T (pos _)    = ⊥
  T (negsuc _) = ℕ

injNeg : ∀ {a b : ℕ} → neg a ≡ neg b → a ≡ b
injNeg {zero} {zero} _ = refl
injNeg {zero} {suc b} nega≡negb = ⊥.rec (posNotnegsuc 0 b nega≡negb)
injNeg {suc a} {zero} nega≡negb = ⊥.rec (negsucNotpos a 0 nega≡negb)
injNeg {suc a} {suc b} nega≡negb = cong suc (injNegsuc nega≡negb)

discreteℤ : Discrete ℤ
discreteℤ (pos n) (pos m) with discreteℕ n m
... | yes p = yes (cong pos p)
... | no p  = no (λ x → p (injPos x))
discreteℤ (pos n) (negsuc m) = no (posNotnegsuc n m)
discreteℤ (negsuc n) (pos m) = no (negsucNotpos n m)
discreteℤ (negsuc n) (negsuc m) with discreteℕ n m
... | yes p = yes (cong negsuc p)
... | no p  = no (λ x → p (injNegsuc x))

isSetℤ : isSet ℤ
isSetℤ = Discrete→isSet discreteℤ

-pos : ∀ n → - (pos n) ≡ neg n
-pos zero    = refl
-pos (suc n) = refl

-neg : ∀ n → - (neg n) ≡ pos n
-neg zero    = refl
-neg (suc n) = refl

sucℤnegsucneg : ∀ n → sucℤ (negsuc n) ≡ neg n
sucℤnegsucneg zero = refl
sucℤnegsucneg (suc n) = refl

-sucℤ : ∀ n → - sucℤ n ≡ predℤ (- n)
-sucℤ (pos zero)       = refl
-sucℤ (pos (suc n))    = refl
-sucℤ (negsuc zero)    = refl
-sucℤ (negsuc (suc n)) = refl

-predℤ : ∀ n → - predℤ n ≡ sucℤ (- n)
-predℤ (pos zero)       = refl
-predℤ (pos (suc n))    = -pos n ∙ sym (sucℤnegsucneg n)
-predℤ (negsuc zero)    = refl
-predℤ (negsuc (suc n)) = refl

-Involutive : ∀ z → - (- z) ≡ z
-Involutive (pos n)    = cong -_ (-pos n) ∙ -neg n
-Involutive (negsuc n) = refl

isEquiv- : isEquiv (-_)
isEquiv- = isoToIsEquiv (iso -_ -_ -Involutive -Involutive)

sucℤ+pos : ∀ n m → sucℤ (m +pos n) ≡ (sucℤ m) +pos n
sucℤ+pos zero m = refl
sucℤ+pos (suc n) m = cong sucℤ (sucℤ+pos n m)

predℤ+negsuc : ∀ n m → predℤ (m +negsuc n) ≡ (predℤ m) +negsuc n
predℤ+negsuc zero m = refl
predℤ+negsuc (suc n) m = cong predℤ (predℤ+negsuc n m)

sucℤ+negsuc : ∀ n m → sucℤ (m +negsuc n) ≡ (sucℤ m) +negsuc n
sucℤ+negsuc zero m = (sucPred _) ∙ (sym (predSuc _))
sucℤ+negsuc (suc n) m =      _ ≡⟨ sucPred _ ⟩
  m +negsuc n                    ≡[ i ]⟨ predSuc m (~ i) +negsuc n ⟩
  (predℤ (sucℤ m)) +negsuc n ≡⟨ sym (predℤ+negsuc n (sucℤ m)) ⟩
  predℤ (sucℤ m +negsuc n) ∎

predℤ+pos : ∀ n m → predℤ (m +pos n) ≡ (predℤ m) +pos n
predℤ+pos zero m = refl
predℤ+pos (suc n) m =     _ ≡⟨ predSuc _ ⟩
  m +pos n                    ≡[ i ]⟨ sucPred m (~ i) + pos n ⟩
  (sucℤ (predℤ m)) +pos n ≡⟨ sym (sucℤ+pos n (predℤ m))⟩
  (predℤ m) +pos (suc n)    ∎

predℤ-pos : ∀ n → predℤ(- (pos n)) ≡ negsuc n
predℤ-pos zero = refl
predℤ-pos (suc n) = refl

predℤ+ : ∀ m n → predℤ (m + n) ≡ (predℤ m) + n
predℤ+ m (pos n) = predℤ+pos n m
predℤ+ m (negsuc n) = predℤ+negsuc n m

+predℤ : ∀ m n → predℤ (m + n) ≡ m + (predℤ n)
+predℤ m (pos zero) = refl
+predℤ m (pos (suc n)) = (predSuc (m + pos n)) ∙ (cong (_+_ m) (sym (predSuc (pos n))))
+predℤ m (negsuc n) = refl

sucℤ+ : ∀ m n → sucℤ (m + n) ≡ (sucℤ m) + n
sucℤ+ m (pos n) = sucℤ+pos n m
sucℤ+ m (negsuc n) = sucℤ+negsuc n m

+sucℤ : ∀ m n → sucℤ (m + n) ≡  m + (sucℤ n)
+sucℤ m (pos n) = refl
+sucℤ m (negsuc zero) = sucPred _
+sucℤ m (negsuc (suc n)) = (sucPred (m +negsuc n)) ∙ (cong (_+_ m) (sym (sucPred (negsuc n))))

pos0+ : ∀ z → z ≡ pos 0 + z
pos0+ (pos zero) = refl
pos0+ (pos (suc n)) = cong sucℤ (pos0+ (pos n))
pos0+ (negsuc zero) = refl
pos0+ (negsuc (suc n)) = cong predℤ (pos0+ (negsuc n))

negsuc0+ : ∀ z → predℤ z ≡ negsuc 0 + z
negsuc0+ (pos zero) = refl
negsuc0+ (pos (suc n)) = (sym (sucPred (pos n))) ∙ (cong sucℤ (negsuc0+ _))
negsuc0+ (negsuc zero) = refl
negsuc0+ (negsuc (suc n)) = cong predℤ (negsuc0+ (negsuc n))

ind-comm : {A : Type₀} (_∙_ : A → A → A) (f : ℕ → A) (g : A → A)
           (p : ∀ {n} → f (suc n) ≡ g (f n))
           (g∙ : ∀ a b → g (a ∙ b) ≡ g a ∙ b)
           (∙g : ∀ a b → g (a ∙ b) ≡ a ∙ g b)
           (base : ∀ z → z ∙ f 0 ≡ f 0 ∙ z)
         → ∀ z n → z ∙ f n ≡ f n ∙ z
ind-comm _∙_ f g p g∙ ∙g base z 0 = base z
ind-comm _∙_ f g p g∙ ∙g base z (suc n) =
  z ∙ f (suc n) ≡[ i ]⟨ z ∙ p {n} i ⟩
  z ∙ g (f n)   ≡⟨ sym ( ∙g z (f n)) ⟩
  g (z ∙ f n)   ≡⟨ cong g IH ⟩
  g (f n ∙ z)   ≡⟨ g∙ (f n) z ⟩
  g (f n) ∙ z   ≡[ i ]⟨ p {n} (~ i) ∙ z ⟩
  f (suc n) ∙ z ∎
  where
  IH = ind-comm _∙_ f g p g∙ ∙g base z n

ind-assoc : {A : Type₀} (_·_ : A → A → A) (f : ℕ → A)
        (g : A → A) (p : ∀ a b → g (a · b) ≡ a · (g b))
        (q : ∀ {c} → f (suc c) ≡ g (f c))
        (base : ∀ m n → (m · n) · (f 0) ≡ m · (n · (f 0)))
        (m n : A) (o : ℕ)
      → m · (n · (f o)) ≡ (m · n) · (f o)
ind-assoc _·_ f g p q base m n 0 = sym (base m n)
ind-assoc _·_ f g p q base m n (suc o) =
    m · (n · (f (suc o))) ≡[ i ]⟨ m · (n · q {o} i) ⟩
    m · (n · (g (f o)))   ≡[ i ]⟨ m · (p n (f o) (~ i)) ⟩
    m · (g (n · (f o)))   ≡⟨ sym (p m (n · (f o)))⟩
    g (m · (n · (f o)))   ≡⟨ cong g IH ⟩
    g ((m · n) · (f o))   ≡⟨ p (m · n) (f o) ⟩
    (m · n) · (g (f o))   ≡[ i ]⟨ (m · n) · q {o} (~ i) ⟩
    (m · n) · (f (suc o)) ∎
    where
    IH = ind-assoc _·_ f g p q base m n o

+Comm : ∀ m n → m + n ≡ n + m
+Comm m (pos n) = ind-comm _+_ pos sucℤ refl sucℤ+ +sucℤ pos0+ m n
+Comm m (negsuc n) = ind-comm _+_ negsuc predℤ refl predℤ+ +predℤ negsuc0+ m n

+Assoc : ∀ m n o → m + (n + o) ≡ (m + n) + o
+Assoc m n (pos o) = ind-assoc _+_ pos sucℤ +sucℤ refl (λ _ _ → refl) m n o
+Assoc m n (negsuc o) = ind-assoc _+_ negsuc predℤ +predℤ refl +predℤ m n o

-- Compose sucPathℤ with itself n times. Transporting along this
-- will be addition, transporting with it backwards will be subtraction.
-- Use this to define _+'_ for which is easier to prove
-- isEquiv (λ n → n +' m) since _+'_ is defined by transport

sucPathℤ : ℤ ≡ ℤ
sucPathℤ = ua (sucℤ , isoToIsEquiv (iso sucℤ predℤ sucPred predSuc))

addEq : ℕ → ℤ ≡ ℤ
addEq zero = refl
addEq (suc n) = (addEq n) ∙ sucPathℤ

predPathℤ : ℤ ≡ ℤ
predPathℤ = ua (predℤ , isoToIsEquiv (iso predℤ sucℤ predSuc sucPred))

subEq : ℕ → ℤ ≡ ℤ
subEq zero = refl
subEq (suc n) = (subEq n) ∙ predPathℤ

_+'_ : ℤ → ℤ → ℤ
m +' pos n    = transport (addEq n) m
m +' negsuc n = transport (subEq (suc n)) m

+'≡+ : _+'_ ≡ _+_
+'≡+ i m (pos zero) = m
+'≡+ i m (pos (suc n)) = sucℤ (+'≡+ i m (pos n))
+'≡+ i m (negsuc zero) = predℤ m
+'≡+ i m (negsuc (suc n)) = predℤ (+'≡+ i m (negsuc n)) --
  -- compPath (λ i → (+'≡+ i (predℤ m) (negsuc n))) (sym (predℤ+negsuc n m)) i

isEquivAddℤ' : (m : ℤ) → isEquiv (λ n → n +' m)
isEquivAddℤ' (pos n)    = isEquivTransport (addEq n)
isEquivAddℤ' (negsuc n) = isEquivTransport (subEq (suc n))

isEquivAddℤ : (m : ℤ) → isEquiv (λ n → n + m)
isEquivAddℤ = subst (λ add → (m : ℤ) → isEquiv (λ n → add n m)) +'≡+ isEquivAddℤ'

-- below is an alternate proof of isEquivAddℤ for comparison
-- We also have two useful lemma here.

minusPlus : ∀ m n → (n - m) + m ≡ n
minusPlus (pos zero) n = refl
minusPlus (pos 1) = sucPred
minusPlus (pos (suc (suc m))) n =
  sucℤ ((n +negsuc (suc m)) +pos (suc m)) ≡⟨ sucℤ+pos (suc m) _ ⟩
  sucℤ (n +negsuc (suc m)) +pos (suc m)   ≡[ i ]⟨ sucPred (n +negsuc m) i +pos (suc m) ⟩
  (n - pos (suc m)) +pos (suc m)            ≡⟨ minusPlus (pos (suc m)) n ⟩
  n ∎
minusPlus (negsuc zero) = predSuc
minusPlus (negsuc (suc m)) n =
  predℤ (sucℤ (sucℤ (n +pos m)) +negsuc m) ≡⟨ predℤ+negsuc m _ ⟩
  predℤ (sucℤ (sucℤ (n +pos m))) +negsuc m ≡[ i ]⟨ predSuc (sucℤ (n +pos m)) i +negsuc m ⟩
  sucℤ (n +pos m) +negsuc m                    ≡⟨ minusPlus (negsuc m) n ⟩
  n ∎

-≡0 : (m n : ℤ) → m - n ≡ 0 → m ≡ n
-≡0 m n p = sym (subst (λ a → a + n ≡ m) p (minusPlus n m)) ∙ +Comm 0 n

plusMinus : ∀ m n → (n + m) - m ≡ n
plusMinus (pos zero) n = refl
plusMinus (pos (suc m)) = minusPlus (negsuc m)
plusMinus (negsuc m) = minusPlus (pos (suc m))

private
  alternateProof : (m : ℤ) → isEquiv (λ n → n + m)
  alternateProof m = isoToIsEquiv (iso (λ n → n + m)
                                       (λ n → n - m)
                                       (minusPlus m)
                                       (plusMinus m))

-Cancel : ∀ z → z - z ≡ 0
-Cancel z = cong (_- z) (pos0+ z) ∙ plusMinus z (pos zero)

-Cancel' : ∀ z → - z + z ≡ 0
-Cancel' z = +Comm (- z) z ∙ -Cancel z

pos+ : ∀ m n → pos (m +ℕ n) ≡ pos m + pos n
pos+ zero zero = refl
pos+ zero (suc n)    =
  pos (zero +ℕ suc n)    ≡⟨ +Comm (pos (suc n)) (pos zero) ⟩
  pos zero + pos (suc n) ∎
pos+ (suc m) zero    =
  pos (suc (m +ℕ zero))  ≡⟨ cong pos (cong suc (+-zero m)) ⟩
  pos (suc m) + pos zero ∎
pos+ (suc m) (suc n) =
  pos (suc m +ℕ suc n)            ≡⟨ cong pos (cong suc (+-suc m n)) ⟩
  sucℤ (pos (suc (m +ℕ n)))     ≡⟨ cong sucℤ (cong sucℤ (pos+ m n)) ⟩
  sucℤ (sucℤ (pos m + pos n)) ≡⟨ sucℤ+ (pos m) (sucℤ (pos n)) ⟩
  pos (suc m) + pos (suc n)       ∎

negsuc+ : ∀ m n → negsuc (m +ℕ n) ≡ negsuc m - pos n
negsuc+ zero zero       = refl
negsuc+ zero (suc n)    =
  negsuc (zero +ℕ suc n)    ≡⟨ negsuc0+ (negsuc n) ⟩
  negsuc zero + negsuc n    ≡⟨ cong (negsuc zero +_) (-pos (suc n)) ⟩
  negsuc zero - pos (suc n) ∎
negsuc+ (suc m) zero    =
  negsuc (suc m +ℕ zero)    ≡⟨ cong negsuc (cong suc (+-zero m)) ⟩
  negsuc (suc m) - pos zero ∎
negsuc+ (suc m) (suc n) =
  negsuc (suc m +ℕ suc n)        ≡⟨ cong negsuc (sym (+-suc m (suc n))) ⟩
  negsuc (m +ℕ suc (suc n))      ≡⟨ negsuc+ m (suc (suc n)) ⟩
  negsuc m - pos (suc (suc n))   ≡⟨ sym (+predℤ (negsuc m) (negsuc n)) ⟩
  predℤ (negsuc m + negsuc n ) ≡⟨ predℤ+ (negsuc m) (negsuc n) ⟩
  negsuc (suc m) - pos (suc n)   ∎

neg+ : ∀ m n → neg (m +ℕ n) ≡ neg m + neg n
neg+ zero zero       = refl
neg+ zero (suc n)    = neg (zero +ℕ suc n)    ≡⟨ +Comm (neg (suc n)) (pos zero) ⟩
                       neg zero + neg (suc n) ∎
neg+ (suc m) zero    = neg (suc (m +ℕ zero))  ≡⟨ cong neg (cong suc (+-zero m)) ⟩
                       neg (suc m) + neg zero ∎
neg+ (suc m) (suc n) = neg (suc m +ℕ suc n)      ≡⟨ negsuc+ m (suc n) ⟩
                       neg (suc m) + neg (suc n) ∎

ℕ-AntiComm : ∀ m n → m ℕ- n ≡ - (n ℕ- m)
ℕ-AntiComm zero zero       = refl
ℕ-AntiComm zero (suc n)    = refl
ℕ-AntiComm (suc m) zero    = refl
ℕ-AntiComm (suc m) (suc n) = suc m ℕ- suc n  ≡⟨ ℕ-AntiComm m n ⟩
                          - (suc n ℕ- suc m) ∎

pos- : ∀ m n → m ℕ- n ≡ pos m - pos n
pos- zero zero       = refl
pos- zero (suc n)    = zero ℕ- suc n          ≡⟨ +Comm (negsuc n) (pos zero) ⟩
                       pos zero - pos (suc n) ∎
pos- (suc m) zero    = refl
pos- (suc m) (suc n) =
  suc m ℕ- suc n                       ≡⟨ pos- m n ⟩
  pos m - pos n                        ≡⟨ sym (sucPred (pos m - pos n)) ⟩
  sucℤ (predℤ (pos m - pos n))     ≡⟨ cong sucℤ (+predℤ (pos m) (- pos n)) ⟩
  sucℤ (pos m + predℤ (- (pos n))) ≡⟨ cong sucℤ (cong (pos m +_) (predℤ-pos n)) ⟩
  sucℤ (pos m + negsuc n)            ≡⟨ sucℤ+negsuc n (pos m) ⟩
  pos (suc m) - pos (suc n)            ∎

-AntiComm : ∀ m n → m - n ≡ - (n - m)
-AntiComm (pos n) (pos m)       = pos n - pos m   ≡⟨ sym (pos- n m) ⟩
                                   n ℕ- m         ≡⟨ ℕ-AntiComm n m ⟩
                                - (m ℕ- n)        ≡⟨ cong -_ (pos- m n) ⟩
                                - (pos m - pos n) ∎
-AntiComm (pos n) (negsuc m)    =
     pos n - negsuc m     ≡⟨ +Comm (pos n) (pos (suc m)) ⟩
     pos (suc m) + pos n  ≡⟨ sym (pos+ (suc m) n) ⟩
     pos (suc m +ℕ n)     ≡⟨ sym (-neg (suc m +ℕ n)) ⟩
  -  neg (suc m +ℕ n)     ≡⟨ cong -_ (neg+ (suc m) n) ⟩
  - (neg (suc m) + neg n) ≡⟨ cong -_ (cong (negsuc m +_) (sym (-pos n))) ⟩
  - (negsuc m - pos n)    ∎
-AntiComm (negsuc n) (pos m)    =
     negsuc n - pos m     ≡⟨ sym (negsuc+ n m) ⟩
     negsuc (n +ℕ m)      ≡⟨ cong -_ (pos+ (suc n) m) ⟩
  - (pos (suc n) + pos m) ≡⟨ cong -_ (+Comm (pos (suc n)) (pos m)) ⟩
  - (pos m - negsuc n)    ∎
-AntiComm (negsuc n) (negsuc m) =
     negsuc n - negsuc m        ≡⟨ +Comm (negsuc n) (pos (suc m)) ⟩
     pos (suc m) + negsuc n     ≡⟨ sym (pos- (suc m) (suc n)) ⟩
     suc m ℕ- suc n             ≡⟨ ℕ-AntiComm (suc m) (suc n) ⟩
  - (suc n ℕ- suc m)            ≡⟨ cong -_ (pos- (suc n) (suc m)) ⟩
  - (pos (suc n) - pos (suc m)) ≡⟨ cong -_ (+Comm (pos (suc n)) (negsuc m)) ⟩
  - (negsuc m - negsuc n)       ∎

-Dist+ : ∀ m n → - (m + n) ≡ (- m) + (- n)
-Dist+ (pos n) (pos m)       =
   - (pos n + pos m)     ≡⟨ cong -_ (sym (pos+ n m)) ⟩
   -  pos (n +ℕ m)       ≡⟨ -pos (n +ℕ m) ⟩
      neg (n +ℕ m)       ≡⟨ neg+ n m ⟩
      neg n + neg m      ≡⟨ cong (neg n +_) (sym (-pos m)) ⟩
      neg n + (- pos m)  ≡⟨ cong (_+ (- pos m)) (sym (-pos n)) ⟩
  (-  pos n) + (- pos m) ∎
-Dist+ (pos n) (negsuc m)    =
   - (pos n + negsuc m)     ≡⟨ sym (-AntiComm (pos (suc m)) (pos n)) ⟩
      pos (suc m) - pos n   ≡⟨ +Comm (pos (suc m)) (- pos n) ⟩
  (-  pos n) + (- negsuc m) ∎
-Dist+ (negsuc n) (pos m)    =
   - (negsuc n + pos m)     ≡⟨ cong -_ (+Comm (negsuc n) (pos m)) ⟩
   - (pos m + negsuc n)     ≡⟨ sym (-AntiComm (- negsuc n) (pos m)) ⟩
  (-  negsuc n) + (- pos m) ∎
-Dist+ (negsuc n) (negsuc m) =
   - (negsuc n + negsuc m)     ≡⟨ cong -_ (sym (neg+ (suc n) (suc m))) ⟩
   -  neg (suc n +ℕ suc m)     ≡⟨ pos+ (suc n) (suc m) ⟩
  (-  negsuc n) + (- negsuc m) ∎

-DistMin : ∀ m n → - min m n ≡ max (- m) (- n)
-DistMin (pos zero) (pos zero) = refl
-DistMin (pos zero) (pos (suc n)) = refl
-DistMin (pos (suc m)) (pos zero) = refl
-DistMin (pos (suc m)) (pos (suc n)) = -sucℤ (min (pos m) (pos n)) ∙
                                       cong predℤ (-DistMin (pos m) (pos n)) ∙
                                       predDistMax (- pos m) (- pos n) ∙
                                       cong₂ max (sym (-sucℤ (pos m)))
                                                 (sym (-sucℤ (pos n)))
-DistMin (pos zero) (negsuc zero) = refl
-DistMin (pos zero) (negsuc (suc n)) = refl
-DistMin (pos (suc m)) (negsuc zero) = refl
-DistMin (pos (suc m)) (negsuc (suc n)) = refl
-DistMin (negsuc zero) (negsuc zero) = refl
-DistMin (negsuc zero) (negsuc (suc n)) = refl
-DistMin (negsuc (suc m)) (pos zero) = refl
-DistMin (negsuc (suc m)) (pos (suc n)) = refl
-DistMin (negsuc zero) (pos zero) = refl
-DistMin (negsuc zero) (pos (suc n)) = refl
-DistMin (negsuc (suc m)) (negsuc zero) = refl
-DistMin (negsuc (suc m)) (negsuc (suc n)) = -predℤ (min (negsuc m) (negsuc n)) ∙
                                             cong sucℤ (-DistMin (negsuc m) (negsuc n))

-DistMax : ∀ m n → - max m n ≡ min (- m ) (- n)
-DistMax (pos zero) (pos zero) = refl
-DistMax (pos zero) (pos (suc n)) = refl
-DistMax (pos (suc m)) (pos zero) = refl
-DistMax (pos (suc m)) (pos (suc n)) = -sucℤ (max (pos m) (pos n)) ∙
                                       cong predℤ (-DistMax (pos m) (pos n)) ∙
                                       predDistMin (- pos m) (- pos n) ∙
                                       cong₂ min (sym (-sucℤ (pos m)))
                                                 (sym (-sucℤ (pos n)))
-DistMax (pos zero) (negsuc zero) = refl
-DistMax (pos zero) (negsuc (suc n)) = refl
-DistMax (pos (suc m)) (negsuc zero) = refl
-DistMax (pos (suc m)) (negsuc (suc n)) = refl
-DistMax (negsuc zero) (pos zero) = refl
-DistMax (negsuc zero) (pos (suc n)) = refl
-DistMax (negsuc (suc m)) (pos zero) = refl
-DistMax (negsuc (suc m)) (pos (suc n)) = refl
-DistMax (negsuc zero) (negsuc zero) = refl
-DistMax (negsuc zero) (negsuc (suc n)) = refl
-DistMax (negsuc (suc m)) (negsuc zero) = refl
-DistMax (negsuc (suc m)) (negsuc (suc n)) = -predℤ (max (negsuc m) (negsuc n)) ∙
                                             cong sucℤ (-DistMax (negsuc m) (negsuc n))

min- : ∀ x y → min (pos x) (- (pos y)) ≡ - (pos y)
min- zero zero       = refl
min- zero (suc y)    = refl
min- (suc x) zero    = refl
min- (suc x) (suc y) = refl

-min : ∀ x y → min (- (pos x)) (pos y) ≡ - (pos x)
-min x y = minComm (- (pos x)) (pos y) ∙ min- y x

max- : ∀ x y → max (pos x) (- (pos y)) ≡ pos x
max- zero zero       = refl
max- zero (suc y)    = refl
max- (suc x) zero    = refl
max- (suc x) (suc y) = refl

-max : ∀ x y → max (- (pos x)) (pos y) ≡ pos y
-max x y = maxComm (- (pos x)) (pos y) ∙ max- y x

inj-z+ : ∀ {z l n} → z + l ≡ z + n → l ≡ n
inj-z+ {pos zero} {l} {n} p = l            ≡⟨ pos0+ l ⟩
                              pos zero + l ≡⟨ p ⟩
                              pos zero + n ≡⟨ sym (pos0+ n) ⟩
                              n            ∎
inj-z+ {pos (suc z)} {l} {n} p
  = inj-z+ {z = pos z} (sym (predℤ+ (pos (suc z)) l)
                      ∙ cong predℤ p
                      ∙ predℤ+ (pos (suc z)) n)
inj-z+ {negsuc zero} {l} {n} p = sym (sucPred l)
                               ∙ cong sucℤ (negsuc0+ l
                                 ∙ p
                                 ∙ sym (negsuc0+ n))
                               ∙ sucPred n
inj-z+ {negsuc (suc z)} {l} {n} p
  = inj-z+ {z = negsuc z} (sym (sucℤ+ (negsuc (suc z)) l)
                         ∙ cong sucℤ p
                         ∙ sucℤ+ (negsuc (suc z)) n)

inj-+z : ∀ {z l n} → l + z ≡ n + z → l ≡ n
inj-+z {z} {l} {n} p = inj-z+ {z = z} (+Comm z l ∙ p ∙ +Comm n z)

n+z≡z→n≡0 : ∀ n z → n + z ≡ z → n ≡ 0
n+z≡z→n≡0 n z p = inj-z+ {z = z} {l = n} {n = 0} (+Comm z n ∙ p)

pos+posLposMin : ∀ x y → min (pos (x +ℕ y)) (pos x) ≡ pos x
pos+posLposMin zero y = minComm (pos y) (pos zero)
pos+posLposMin (suc x) zero
  = cong sucℤ (cong (λ a → min a (pos x)) (pos+ x 0) ∙ minIdem (pos x))
pos+posLposMin (suc x) (suc y) = cong sucℤ (pos+posLposMin x (suc y))

pos+posRposMin : ∀ x y → min (pos x) (pos (x +ℕ y)) ≡ pos x
pos+posRposMin x y = minComm (pos x) (pos (x +ℕ y)) ∙ pos+posLposMin x y

pos+posLposMax : ∀ x y → max (pos (x +ℕ y)) (pos x) ≡ pos (x +ℕ y)
pos+posLposMax zero y = maxComm (pos y) (pos zero)
pos+posLposMax (suc x) zero
  = cong sucℤ (cong (λ a → max a (pos x)) (pos+ x 0) ∙ maxIdem (pos x)) ∙
    cong (pos ∘ suc) (sym (+-zero x))
pos+posLposMax (suc x) (suc y) = cong sucℤ (pos+posLposMax x (suc y))

pos+posRposMax : ∀ x y → max (pos x) (pos (x +ℕ y)) ≡ pos (x +ℕ y)
pos+posRposMax x y = maxComm (pos x) (pos (x +ℕ y)) ∙ pos+posLposMax x y

negsuc+posLnegsucMin : ∀ x y → min (negsuc x + pos y) (negsuc x) ≡ negsuc x
negsuc+posLnegsucMin zero zero = refl
negsuc+posLnegsucMin zero (suc y)
  = cong (λ a → min a (negsuc zero))
         (sucℤ+ (negsuc zero) (pos y) ∙ sym (pos0+ (pos y))) ∙
    minComm (pos y) (negsuc zero)
negsuc+posLnegsucMin (suc x) zero = cong predℤ (minIdem (negsuc x))
negsuc+posLnegsucMin (suc x) (suc y)
  = cong (λ a → min a (negsuc (suc x)))
         (sym (predℤ+ (negsuc x) (pos (suc y)))) ∙
    sym (predDistMin (negsuc x + pos (suc y)) (negsuc x)) ∙
    cong predℤ (negsuc+posLnegsucMin x (suc y))

negsuc+posRnegsucMin : ∀ x y → min (negsuc x) (negsuc x + pos y) ≡ negsuc x
negsuc+posRnegsucMin x y = minComm (negsuc x) (negsuc x + pos y) ∙ negsuc+posLnegsucMin x y

negsuc+posLnegsucMax : ∀ x y → max (negsuc x + pos y) (negsuc x) ≡ negsuc x + pos y
negsuc+posLnegsucMax zero zero = refl
negsuc+posLnegsucMax zero (suc y)
  = cong (λ a → max a (negsuc zero))
         (sucℤ+ (negsuc zero) (pos y) ∙ sym (pos0+ (pos y))) ∙
    maxComm (pos y) (negsuc zero) ∙
    pos0+ (pos y) ∙ sym (sucℤ+ (negsuc zero) (pos y))
negsuc+posLnegsucMax (suc x) zero = cong predℤ (maxIdem (negsuc x))
negsuc+posLnegsucMax (suc x) (suc y)
  = cong (λ a → max a (negsuc (suc x)))
         (sym (predℤ+ (negsuc x) (pos (suc y)))) ∙
    sym (predDistMax (negsuc x + pos (suc y)) (negsuc x)) ∙
    cong predℤ (negsuc+posLnegsucMax x (suc y)) ∙
    predℤ+ (negsuc x) (pos (suc y))

negsuc+posRnegsucMax : ∀ x y → max (negsuc x) (negsuc x + pos y) ≡ negsuc x + pos y
negsuc+posRnegsucMax x y = maxComm (negsuc x) (negsuc x + pos y) ∙ negsuc+posLnegsucMax x y

negsuc+negsucLposMin : ∀ x y z → min (negsuc x + negsuc y) (pos z) ≡ negsuc x + negsuc y
negsuc+negsucLposMin x zero z = refl
negsuc+negsucLposMin x (suc y) z
  = cong (λ a → min a (pos z)) (predℤ+ (negsuc x) (negsuc y)) ∙
    negsuc+negsucLposMin (suc x) y z ∙
    sym (predℤ+ (negsuc x) (negsuc y))

negsuc+negsucRposMin : ∀ x y z → min (pos x) (negsuc y + negsuc z) ≡ negsuc y + negsuc z
negsuc+negsucRposMin z x y = minComm (pos z) (negsuc x + negsuc y) ∙ negsuc+negsucLposMin x y z

negsuc+negsucLposMax : ∀ x y z → max (negsuc x + negsuc y) (pos z) ≡ pos z
negsuc+negsucLposMax x zero z = refl
negsuc+negsucLposMax x (suc y) z
  = cong (λ a → max a (pos z))
         (predℤ+ (negsuc x) (negsuc y)) ∙
    negsuc+negsucLposMax (suc x) y z

negsuc+negsucRposMax : ∀ x y z → max (pos x) (negsuc y + negsuc z) ≡ pos x
negsuc+negsucRposMax z x y = maxComm (pos z) (negsuc x + negsuc y) ∙ negsuc+negsucLposMax x y z

negsuc+negsucLnegsucMin : ∀ x y → min (negsuc x + negsuc y) (negsuc x) ≡ negsuc x + negsuc y
negsuc+negsucLnegsucMin zero zero = refl
negsuc+negsucLnegsucMin zero (suc y)
  = cong (λ a → min a (negsuc zero))
         (sym (predℤ+ (pos zero) (negsuc (suc y))) ∙
          cong (predℤ ∘ predℤ) (sym (pos0+ (negsuc y)))) ∙
    cong predℤ (cong predℤ (pos0+ (negsuc y)) ∙
                predℤ+ (pos zero) (negsuc y))
negsuc+negsucLnegsucMin (suc x) zero = cong predℤ (minPredL (negsuc x))
negsuc+negsucLnegsucMin (suc x) (suc y)
  = cong (λ a → min a (negsuc (suc x)))
         (sym (predℤ+ (negsuc x) (negsuc (suc y)))) ∙
    sym (predDistMin (negsuc x + negsuc (suc y)) (negsuc x)) ∙
    cong predℤ (negsuc+negsucLnegsucMin x (suc y) ∙
                predℤ+ (negsuc x) (negsuc y))

negsuc+negsucRnegsucMin : ∀ x y → min (negsuc x) (negsuc x + negsuc y) ≡ negsuc x + negsuc y
negsuc+negsucRnegsucMin x y = minComm (negsuc x) (negsuc x + negsuc y) ∙ negsuc+negsucLnegsucMin x y

negsuc+negsucLnegsucMax : ∀ x y → max (negsuc x + negsuc y) (negsuc x) ≡ negsuc x
negsuc+negsucLnegsucMax zero zero = refl
negsuc+negsucLnegsucMax zero (suc y)
  = cong (λ a → max a (negsuc zero))
         (sym (predℤ+ (pos zero) (negsuc (suc y))) ∙
          cong (predℤ ∘ predℤ) (sym (pos0+ (negsuc y))))
negsuc+negsucLnegsucMax (suc x) zero = cong predℤ (maxPredL (negsuc x))
negsuc+negsucLnegsucMax (suc x) (suc y)
  = cong (λ a → max a (negsuc (suc x)))
         (sym (predℤ+ (negsuc x) (negsuc (suc y)))) ∙
    sym (predDistMax (negsuc x + negsuc (suc y)) (negsuc x)) ∙
    cong predℤ (negsuc+negsucLnegsucMax x (suc y))

negsuc+negsucRnegsucMax : ∀ x y → max (negsuc x) (negsuc x + negsuc y) ≡ negsuc x
negsuc+negsucRnegsucMax x y = maxComm (negsuc x) (negsuc x + negsuc y) ∙ negsuc+negsucLnegsucMax x y

pos+pospos+negsucMin : ∀ x y z → min (pos x + pos y) (pos x + negsuc z) ≡ pos x + negsuc z
pos+pospos+negsucMin zero zero zero = refl
pos+pospos+negsucMin zero zero (suc z)
  = cong (min (pos zero)) (+Comm (pos zero) (negsuc (suc z))) ∙
    pos0+ (negsuc (suc z))
pos+pospos+negsucMin zero (suc y) zero
  = cong (λ a → min a (negsuc zero)) (+Comm (pos zero) (pos (suc y)))
pos+pospos+negsucMin zero (suc y) (suc z)
  = cong₂ min (+Comm (pos zero) (pos (suc y)))
              (+Comm (pos zero) (negsuc (suc z))) ∙
    pos0+ (negsuc (suc z))
pos+pospos+negsucMin (suc x) y z
  = cong₂ min (sym (sucℤ+ (pos x) (pos y)))
              (sym (sucℤ+ (pos x) (negsuc z))) ∙
    sym (sucDistMin (pos x + pos y) (pos x + negsuc z)) ∙
    cong sucℤ (pos+pospos+negsucMin x y z) ∙
    sucℤ+ (pos x) (negsuc z)

pos+pospos+negsucMax : ∀ x y z → max (pos x + pos y) (pos x + negsuc z) ≡ pos x + pos y
pos+pospos+negsucMax zero zero zero = refl
pos+pospos+negsucMax zero zero (suc z) = cong (max (pos zero)) (sym (pos0+ (negsuc (suc z))))
pos+pospos+negsucMax zero (suc y) zero
  = cong (λ a → max a (negsuc zero))
         (sym (pos0+ (pos (suc y)))) ∙
    pos0+ (pos (suc y))
pos+pospos+negsucMax zero (suc y) (suc z)
  = cong₂ max (sym (pos0+ (pos (suc y))))
          (sym (pos0+ (negsuc (suc z)))) ∙
    pos0+ (pos (suc y))
pos+pospos+negsucMax (suc x) y z
  = cong₂ max (sym (sucℤ+ (pos x) (pos y)))
              (sym (sucℤ+ (pos x) (negsuc z))) ∙
    sym (sucDistMax (pos x + pos y) (pos x + negsuc z)) ∙
    cong sucℤ (pos+pospos+negsucMax x y z) ∙ sucℤ+ (pos x) (pos y)

negsuc+negsucnegsuc+posMin : ∀ x y z → min (negsuc x + negsuc y) (negsuc x + pos z)
                           ≡ negsuc x + negsuc y
negsuc+negsucnegsuc+posMin zero zero zero = refl
negsuc+negsucnegsuc+posMin zero zero (suc z)
  = cong (min (negsuc 1))
         (sucℤ+ (negsuc zero) (pos z) ∙ sym (pos0+ (pos z)))
negsuc+negsucnegsuc+posMin zero (suc y) zero = negsuc+negsucLnegsucMin zero (suc y)
negsuc+negsucnegsuc+posMin zero (suc y) (suc z)
  = cong (min (negsuc zero + negsuc (suc y)))
         (sucℤ+ (negsuc zero) (pos z) ∙ sym (pos0+ (pos z))) ∙
    negsuc+negsucLposMin zero (suc y) z
negsuc+negsucnegsuc+posMin (suc x) y z
  = cong₂ min (sym (predℤ+ (negsuc x) (negsuc y)))
              (sym (predℤ+ (negsuc x) (pos z))) ∙
    sym (predDistMin (negsuc x + negsuc y) (negsuc x + pos z)) ∙
    cong predℤ (negsuc+negsucnegsuc+posMin x y z) ∙
    predℤ+ (negsuc x) (negsuc y)

negsuc+negsucnegsuc+posMax : ∀ x y z → max (negsuc x + negsuc y) (negsuc x + pos z)
                           ≡ negsuc x + pos z
negsuc+negsucnegsuc+posMax zero zero zero = refl
negsuc+negsucnegsuc+posMax zero zero (suc z)
  = cong (max (negsuc 1))
         (sucℤ+ (negsuc zero) (pos z) ∙
          sym (pos0+ (pos z))) ∙
    pos0+ (pos z) ∙
    sym (sucℤ+ (negsuc zero) (pos z))
negsuc+negsucnegsuc+posMax zero (suc y) zero = negsuc+negsucLnegsucMax zero (suc y)
negsuc+negsucnegsuc+posMax zero (suc y) (suc z)
  = cong (max (negsuc zero + negsuc (suc y)))
         (sucℤ+ (negsuc zero) (pos z) ∙ sym (pos0+ (pos z))) ∙
    negsuc+negsucLposMax zero (suc y) z ∙
    pos0+ (pos z) ∙
    sym (sucℤ+ (negsuc zero) (pos z))
negsuc+negsucnegsuc+posMax (suc x) y z
  = cong₂ max (sym (predℤ+ (negsuc x) (negsuc y)))
              (sym (predℤ+ (negsuc x) (pos z))) ∙
    sym (predDistMax (negsuc x + negsuc y) (negsuc x + pos z)) ∙
    cong predℤ (negsuc+negsucnegsuc+posMax x y z) ∙
    predℤ+ (negsuc x) (pos z)

+DistRMin : ∀ x y z → x + min y z ≡ min (x + y) (x + z)
+DistRMin (pos zero) y z = sym (pos0+ (min y z)) ∙ cong₂ min (pos0+ y) (pos0+ z)
+DistRMin (pos (suc x)) (pos zero) (pos zero) = sym (cong sucℤ (minIdem (pos x)))
+DistRMin (pos (suc x)) (pos zero) (pos (suc z))
  = cong sucℤ (+DistRMin (pos x) (pos zero) (pos (suc z))) ∙
    sucDistMin (pos x) (pos x + pos (suc z)) ∙
    cong (min (pos (suc x))) (sucℤ+ (pos x) (pos (suc z)))
+DistRMin (pos (suc x)) (pos (suc y)) (pos zero)
  = cong sucℤ (+DistRMin (pos x) (pos (suc y)) (pos zero)) ∙
    sucDistMin (pos x + pos (suc y)) (pos x) ∙
    cong (λ a → min a (pos (suc x))) (sucℤ+ (pos x) (pos (suc y)))
+DistRMin (pos (suc x)) (pos (suc y)) (pos (suc z))
  = sym (+sucℤ (pos (suc x)) (min (pos y) (pos z))) ∙
    sucℤ+ (pos (suc x)) (min (pos y) (pos z)) ∙
    +DistRMin (pos (suc (suc x))) (pos y) (pos z) ∙
    cong₂ min (sym (sucℤ+ (pos (suc x)) (pos y)) ∙
              +sucℤ (pos (suc x)) (pos y))
              (sym (sucℤ+ (pos (suc x)) (pos z)) ∙
              +sucℤ (pos (suc x)) (pos z))
+DistRMin (pos (suc x)) (pos y) (negsuc z)
  = cong (pos (suc x) +_) (minComm (pos y) (negsuc z)) ∙
    sym (pos+pospos+negsucMin (suc x) y z)
+DistRMin (pos (suc x)) (negsuc y) (pos z)
  = sym (minComm (pos (suc x) + negsuc y) (pos (suc x) + pos z) ∙
         pos+pospos+negsucMin (suc x) z y)
+DistRMin (pos (suc x)) (negsuc zero) (negsuc zero) = sym (minIdem (pos x))
+DistRMin (pos (suc x)) (negsuc zero) (negsuc (suc z))
  = (cong predℤ (sym (sucℤ+ (pos x) (negsuc z))) ∙
     predSuc (pos x + negsuc z)) ∙
     sym (pos+pospos+negsucMin x 0 z) ∙
     cong (min (pos x)) (sym (predSuc (pos x + negsuc z)) ∙
                         cong predℤ (sucℤ+ (pos x) (negsuc z)))
+DistRMin (pos (suc x)) (negsuc (suc y)) (negsuc zero)
  = (cong predℤ (sym (sucℤ+ (pos x) (negsuc y))) ∙
     predSuc (pos x + negsuc y)) ∙
     sym (pos+pospos+negsucMin x 0 y) ∙
     cong (min (pos x))
          (sym (predSuc (pos x + negsuc y)) ∙
          cong predℤ (sucℤ+ (pos x) (negsuc y))) ∙
     minComm (pos x) (pos (suc x) + negsuc (suc y))
+DistRMin (pos (suc x)) (negsuc (suc y)) (negsuc (suc z))
  = sym (+predℤ (pos (suc x)) (min (negsuc y) (negsuc z))) ∙
    predℤ+ (pos (suc x)) (min (negsuc y) (negsuc z)) ∙
    +DistRMin (pos x) (negsuc y) (negsuc z) ∙
    cong₂ min (cong (_+ negsuc y) (sym (predSuc (pos x))) ∙
               sym (predℤ+ (pos (suc x)) (negsuc y)))
              (cong (_+ negsuc z) (sym (predSuc (pos x))) ∙
               sym (predℤ+ (pos (suc x)) (negsuc z)))
+DistRMin (negsuc x) (pos zero) (pos zero) = sym (minIdem (negsuc x))
+DistRMin (negsuc x) (pos zero) (pos (suc z)) = sym (negsuc+posRnegsucMin x (suc z))
+DistRMin (negsuc x) (pos (suc y)) (pos zero) = sym (negsuc+posLnegsucMin x (suc y))
+DistRMin (negsuc zero) (pos (suc y)) (pos (suc z))
  = sym (+sucℤ (negsuc zero) (min (pos y) (pos z))) ∙
    sucℤ+ (negsuc zero) (min (pos y) (pos z)) ∙
    sym (pos0+ (min (pos y) (pos z))) ∙
    cong₂ min (pos0+ (pos y) ∙ sym (sucℤ+ (negsuc zero) (pos y)))
              (pos0+ (pos z) ∙ sym (sucℤ+ (negsuc zero) (pos z)))
+DistRMin (negsuc (suc x)) (pos (suc y)) (pos (suc z))
  = sym (+sucℤ (negsuc (suc x)) (min (pos y) (pos z))) ∙
    cong sucℤ (+DistRMin (negsuc (suc x)) (pos y) (pos z)) ∙
    sucDistMin (negsuc (suc x) + pos y) (negsuc (suc x) + pos z)
+DistRMin (negsuc x) (pos y) (negsuc z)
  = cong (negsuc x +_) (minComm (pos y) (negsuc z)) ∙
    sym (negsuc+negsucnegsuc+posMin x z y) ∙
    minComm (negsuc x + negsuc z) (negsuc x + pos y)
+DistRMin (negsuc x) (negsuc y) (pos z) = sym (negsuc+negsucnegsuc+posMin x y z)
+DistRMin (negsuc zero) (negsuc zero) (negsuc zero) = refl
+DistRMin (negsuc zero) (negsuc zero) (negsuc (suc z))
  = sym (cong (min (negsuc 1)) (predℤ+ (negsuc zero) (negsuc z)) ∙
    negsuc+negsucRnegsucMin 1 z ∙
    sym (predℤ+ (negsuc zero) (negsuc z)))
+DistRMin (negsuc zero) (negsuc (suc y)) (negsuc zero)
  = sym (cong (λ a → min a (negsuc 1)) (predℤ+ (negsuc zero) (negsuc y)) ∙
    negsuc+negsucLnegsucMin 1 y ∙
    sym (predℤ+ (negsuc zero) (negsuc y)))
+DistRMin (negsuc zero) (negsuc (suc y)) (negsuc (suc z))
  = sym (+predℤ (negsuc zero) (min (negsuc y) (negsuc z))) ∙
    predℤ+ (negsuc zero) (min (negsuc y) (negsuc z)) ∙
    +DistRMin (negsuc 1) (negsuc y) (negsuc z) ∙
    cong₂ min (sym (predℤ+ (negsuc zero) (negsuc y)))
              (sym (predℤ+ (negsuc zero) (negsuc z)))
+DistRMin (negsuc (suc x)) (negsuc zero) (negsuc zero)
  = sym (cong (predℤ ∘ predℤ) (minIdem (negsuc x)))
+DistRMin (negsuc (suc x)) (negsuc zero) (negsuc (suc z))
  = sym (sym (predDistMin (negsuc (suc x)) (negsuc (suc x) + negsuc z)) ∙
         cong predℤ (negsuc+negsucRnegsucMin (suc x) z))
+DistRMin (negsuc (suc x)) (negsuc (suc y)) (negsuc zero)
  = sym (sym (predDistMin (negsuc (suc x) + negsuc y) (negsuc (suc x))) ∙
         cong predℤ (negsuc+negsucLnegsucMin (suc x) y))
+DistRMin (negsuc (suc x)) (negsuc (suc y)) (negsuc (suc z))
  = sym (+predℤ (negsuc (suc x)) (min (negsuc y) (negsuc z))) ∙
    cong predℤ (+DistRMin (negsuc (suc x)) (negsuc y) (negsuc z)) ∙
    predDistMin (negsuc (suc x) + negsuc y) (negsuc (suc x) + negsuc z)

+DistLMin : ∀ x y z → min x y + z ≡ min (x + z) (y + z)
+DistLMin x y z
  = +Comm (min x y) z ∙
    +DistRMin z x y ∙
    cong₂ min (+Comm z x)
              (+Comm z y)

+DistRMax : ∀ x y z → x + max y z ≡ max (x + y) (x + z)
+DistRMax x y z
  = sym (-Involutive (x + max y z)) ∙
    cong -_ (-Dist+ x (max y z) ∙
             cong (- x +_) (-DistMax y z) ∙
                  +DistRMin (- x) (- y) (- z)) ∙
             -DistMin (- x - y) (- x - z) ∙
    cong₂ max (-Dist+ (- x) (- y) ∙
               cong₂ _+_ (-Involutive x)
                         (-Involutive y))
              (-Dist+ (- x) (- z) ∙
               cong₂ _+_ (-Involutive x)
                         (-Involutive z))

+DistLMax : ∀ x y z → max x y + z ≡ max (x + z) (y + z)
+DistLMax x y z
  = +Comm (max x y) z ∙
    +DistRMax z x y ∙
    cong₂ max (+Comm z x)
              (+Comm z y)

-- multiplication

pos·pos : (n m : ℕ) → pos (n ·ℕ m) ≡ pos n · pos m
pos·pos zero m = refl
pos·pos (suc n) m = pos+ m (n ·ℕ m) ∙ cong (pos m +_) (pos·pos n m)

pos·negsuc : (n m : ℕ) → pos n · negsuc m ≡ - (pos n · pos (suc m))
pos·negsuc zero m = refl
pos·negsuc (suc n) m =
     (λ i → negsuc m + (pos·negsuc n m i))
   ∙ sym (-Dist+ (pos (suc m)) (pos n · pos (suc m)))

negsuc·pos : (n m : ℕ) → negsuc n · pos m ≡ - (pos (suc n) · pos m)
negsuc·pos zero m = refl
negsuc·pos (suc n) m =
    cong ((- pos m) +_) (negsuc·pos n m)
  ∙ sym (-Dist+ (pos m) (pos m + (pos n · pos m)))

negsuc·negsuc : (n m : ℕ) → negsuc n · negsuc m ≡ pos (suc n) · pos (suc m)
negsuc·negsuc zero m = refl
negsuc·negsuc (suc n) m = cong (pos (suc m) +_) (negsuc·negsuc n m)

·Comm : (x y : ℤ) → x · y ≡ y · x
·Comm (pos n) (pos m) = lem n m
  where
  lem : (n m : ℕ) → (pos n · pos m) ≡ (pos m · pos n)
  lem zero zero = refl
  lem zero (suc m) i = +Comm (lem zero m i) (pos zero) i
  lem (suc n) zero i = +Comm (pos zero) (lem n zero i) i
  lem (suc n) (suc m) =
       (λ i → pos (suc m) + (lem n (suc m) i))
    ∙∙ +Assoc (pos (suc m)) (pos n) (pos m · pos n)
    ∙∙ (λ i → sucℤ+ (pos m) (pos n) (~ i)  + (pos m · pos n))
    ∙∙ (λ i → +Comm (pos m) (pos (suc n)) i + (pos m · pos n))
    ∙∙ sym (+Assoc (pos (suc n)) (pos m) (pos m · pos n))
    ∙∙ (λ i → pos (suc n) + (pos m + (lem n m (~ i))))
    ∙∙ λ i → pos (suc n) + (lem (suc n) m i)
·Comm (pos n) (negsuc m) =
     pos·negsuc n m
  ∙∙ cong -_ (·Comm (pos n) (pos (suc m)))
  ∙∙ sym (negsuc·pos m n)
·Comm (negsuc n) (pos m) =
  sym (pos·negsuc m n
  ∙∙ cong -_ (·Comm (pos m) (pos (suc n)))
  ∙∙ sym (negsuc·pos n m))
·Comm (negsuc n) (negsuc m) =
  negsuc·negsuc n m ∙∙ ·Comm (pos (suc n)) (pos (suc m)) ∙∙ sym (negsuc·negsuc m n)

·IdR : (x : ℤ) → x · 1 ≡ x
·IdR x = ·Comm x 1

·IdL : (x : ℤ) → 1 · x ≡ x
·IdL x = refl

·AnnihilR : (x : ℤ) → x · 0 ≡ 0
·AnnihilR x = ·Comm x 0

·AnnihilL : (x : ℤ) → 0 · x ≡ 0
·AnnihilL x = refl

private
  distrHelper : (x y z w : ℤ) → (x + y) + (z + w) ≡ ((x + z) + (y + w))
  distrHelper x y z w =
      +Assoc (x + y) z w
   ∙∙ cong (_+ w) (sym (+Assoc x y z) ∙∙ cong (x +_) (+Comm y z) ∙∙ +Assoc x z y)
   ∙∙ sym (+Assoc (x + z) y w)

·DistR+ : (x y z : ℤ) → x · (y + z) ≡ x · y + x · z
·DistR+ (pos zero) y z = refl
·DistR+ (pos (suc n)) y z =
     cong ((y + z) +_) (·DistR+ (pos n) y z)
   ∙ distrHelper y z (pos n · y) (pos n · z)
·DistR+ (negsuc zero) y z = -Dist+ y z
·DistR+ (negsuc (suc n)) y z =
    cong₂ _+_ (-Dist+ y z) (·DistR+ (negsuc n) y z)
  ∙ distrHelper (- y) (- z) (negsuc n · y) (negsuc n · z)

·DistL+ : (x y z : ℤ) → (x + y) · z ≡ x · z + y · z
·DistL+ x y z = ·Comm (x + y) z ∙∙ ·DistR+ z x y ∙∙ cong₂ _+_ (·Comm z x) (·Comm z y)

-DistL· : (b c : ℤ) → - (b · c) ≡ - b · c
-DistL· (pos zero) c = refl
-DistL· (pos (suc n)) (pos m) = sym (negsuc·pos n m)
-DistL· (pos (suc zero)) (negsuc m) =
    -Dist+ (negsuc m) (pos zero · negsuc m)
  ∙ cong (pos (suc m) +_) (-DistL· (pos zero) (negsuc m))
-DistL· (pos (suc (suc n))) (negsuc m) =
    -Dist+ (negsuc m) (pos (suc n) · negsuc m)
  ∙ cong (pos (suc m) +_) (-DistL· (pos (suc n)) (negsuc m))
-DistL· (negsuc zero) c = -Involutive c
-DistL· (negsuc (suc n)) c =
   -Dist+ (- c) (negsuc n · c)
 ∙∙ cong (_+ (- (negsuc n · c))) (-Involutive c)
 ∙∙ cong (c +_) (-DistL· (negsuc n) c)

-DistR· : (b c : ℤ) → - (b · c) ≡ b · - c
-DistR· b c = cong (-_) (·Comm b c) ∙∙ -DistL· c b ∙∙ ·Comm (- c) b

-DistLR· : (b c : ℤ) → b · c ≡ - b · - c
-DistLR· b c = sym (-Involutive (b · c)) ∙ (λ i → - -DistL· b c i) ∙ -DistR· (- b) c

ℤ·negsuc : (n : ℤ) (m : ℕ) → n · negsuc m ≡ - (n · pos (suc m))
ℤ·negsuc (pos n) m = pos·negsuc n m
ℤ·negsuc (negsuc n) m = negsuc·negsuc n m ∙ sym (-DistL· (negsuc n) (pos (suc m)))


·Assoc : (a b c : ℤ) → (a · (b · c)) ≡ ((a · b) · c)
·Assoc (pos zero) b c = refl
·Assoc (pos (suc n)) b c =
      cong ((b · c) +_) (·Assoc (pos n) b c)
   ∙∙ cong₂ _+_ (·Comm b c) (·Comm (pos n · b) c)
   ∙∙ sym (·DistR+ c b (pos n · b))
    ∙ sym (·Comm _ c)
·Assoc (negsuc zero) = -DistL·
·Assoc (negsuc (suc n)) b c =
     cong ((- (b · c)) +_) (·Assoc (negsuc n) b c)
  ∙∙ cong (_+ ((negsuc n · b) · c)) (-DistL· b c)
  ∙∙ sym (·DistL+ (- b) (negsuc n · b) c)

·suc→0 : (a : ℤ) (b : ℕ) → a · pos (suc b) ≡ 0 → a ≡ 0
·suc→0 (pos n) b n·b≡0 = cong pos (sym (0≡n·sm→0≡n (sym (injPos (pos·pos n (suc b) ∙ n·b≡0)))))
·suc→0 (negsuc n) b n·b≡0 = ⊥.rec (snotz
                                     (injNeg
                                      (cong -_ (pos·pos (suc n) (suc b)) ∙
                                       sym (negsuc·pos n (suc b)) ∙
                                       n·b≡0)))

sucℤ· : (a b : ℤ) → sucℤ a · b ≡ b + a · b
sucℤ· (pos a) (pos b) = refl
sucℤ· (pos a) (negsuc b) = refl
sucℤ· (negsuc zero) (pos b) = sym (-Cancel (pos b))
sucℤ· (negsuc (suc a)) (pos b) =
  negsuc a · pos b                     ≡⟨ pos0+ (negsuc a · pos b) ⟩
  pos zero + negsuc a · pos b          ≡⟨ cong (_+ negsuc a · pos b) (sym (-Cancel (pos b))) ⟩
  pos b + - pos b + negsuc a · pos b   ≡⟨ sym (+Assoc (pos b) (- pos b) (negsuc a · pos b)) ⟩
  pos b + (- pos b + negsuc a · pos b) ∎
sucℤ· (negsuc zero) (negsuc b) =
      pos zero                ≡⟨ sym (-Cancel' (pos b)) ⟩
  ((- pos b) +pos b)          ≡⟨ cong (_+pos b) (-pos b) ⟩
     (neg b  +pos b)          ≡⟨ cong (_+pos b) (sym (sucℤnegsucneg b)) ⟩
     (sucℤ (negsuc b) +pos b) ≡⟨ sym (sucℤ+pos b (negsuc b)) ⟩
      sucℤ (negsuc b  +pos b) ∎
sucℤ· (negsuc (suc a)) (negsuc b) =
  negsuc a · negsuc b                              ≡⟨ pos0+ (negsuc a · negsuc b) ⟩
  pos zero + negsuc a · negsuc b                   ≡⟨ cong (_+ negsuc a · negsuc b) (sym (-Cancel' (pos (suc b)))) ⟩
 (negsuc b + (pos (suc b))) + negsuc a · negsuc b  ≡⟨ sym (+Assoc (negsuc b) (pos (suc b)) (negsuc a · negsuc b)) ⟩
  negsuc b + (pos (suc b)   + negsuc a · negsuc b) ∎

·sucℤ : (a b : ℤ) → a · sucℤ b ≡ a · b + a
·sucℤ a b = ·Comm a (sucℤ b) ∙ sucℤ· b a ∙ cong (a +_) (·Comm b a) ∙ +Comm a (a · b)

predℤ· : (a  b : ℤ) → predℤ a · b ≡ - b + a · b
predℤ· (pos zero) b = refl
predℤ· (pos (suc a)) b
  = pos0+ (pos a · b) ∙
    cong (_+ pos a · b) (sym (-Cancel' b)) ∙
    sym (+Assoc (- b) b (pos a · b))
predℤ· (negsuc a) b = refl

·predℤ : (a b : ℤ) → a · predℤ b ≡ a · b - a
·predℤ a b = ·Comm a (predℤ b) ∙ predℤ· b a ∙ cong ((- a) +_) (·Comm b a) ∙ +Comm (- a) (a · b)

·DistPosRMin : (x : ℕ) (y z : ℤ) → pos x · min y z ≡ min (pos x · y) (pos x · z)
·DistPosRMin zero y z = refl
·DistPosRMin (suc x) (pos zero) (pos zero)
  = ·Comm (pos (suc x)) (pos zero) ∙
    cong₂ min (·Comm (pos zero) (pos (suc x)))
              (·Comm (pos zero) (pos (suc x)))
·DistPosRMin (suc x) (pos zero) (pos (suc z))
  = ·Comm (pos (suc x)) (pos zero) ∙
    cong₂ min (·Comm (pos zero) (pos (suc x)))
              (pos·pos (suc x) (suc z))
·DistPosRMin (suc x) (pos (suc y)) (pos zero)
  = ·Comm (pos (suc x)) (pos zero) ∙
    cong₂ min (pos·pos (suc x) (suc y))
              (·Comm (pos zero) (pos (suc x)))
·DistPosRMin (suc x) (pos (suc y)) (pos (suc z))
  = ·sucℤ (pos (suc x)) (min (pos y) (pos z)) ∙
    cong (_+ pos (suc x)) (·DistPosRMin (suc x) (pos y) (pos z)) ∙
    +DistLMin (pos (suc x) · pos y) (pos (suc x) · pos z) (pos (suc x)) ∙
    cong₂ min (sym (·sucℤ (pos (suc x)) (pos y)))
              (sym (·sucℤ (pos (suc x)) (pos z)))
·DistPosRMin (suc x) (pos y) (negsuc z)
  = cong (pos (suc x) ·_) (minComm (pos y) (negsuc z)) ∙
    sym (cong₂ min (sym (pos·pos (suc x) y))
                   (pos·negsuc (suc x) z ∙
                    cong -_ (sym (pos·pos (suc x) (suc z)))) ∙
         min- (suc x ·ℕ y) (suc x ·ℕ suc z) ∙
         cong -_ (pos·pos (suc x) (suc z)) ∙
         sym (pos·negsuc (suc x) z))
·DistPosRMin (suc x) (negsuc y) (pos z)
  = sym (cong₂ min (pos·negsuc (suc x) y ∙
                    cong -_ (sym (pos·pos (suc x) (suc y))))
                   (sym (pos·pos (suc x) z)) ∙
         -min (suc x ·ℕ suc y) (suc x ·ℕ z) ∙
         cong -_ (pos·pos (suc x) (suc y)) ∙
         sym (pos·negsuc (suc x) y))
·DistPosRMin (suc x) (negsuc zero) (negsuc zero)
  = sym (minIdem (pos (suc x) · negsuc zero))
·DistPosRMin (suc x) (negsuc zero) (negsuc (suc z))
  = ·predℤ (pos (suc x)) (negsuc z) ∙
    cong (_- pos (suc x)) (·DistPosRMin (suc x) (pos zero) (negsuc z)) ∙
    +DistLMin (pos (suc x) · pos zero) (pos (suc x) · negsuc z) (- pos (suc x)) ∙
    cong₂ min (cong (_+ negsuc x) (·AnnihilR (pos (suc x))) ∙
               sym (pos0+ (negsuc x)) ∙
               ·Comm (negsuc zero) (pos (suc x)))
              (sym (·predℤ (pos (suc x)) (negsuc z)))
·DistPosRMin (suc x) (negsuc (suc y)) (negsuc zero)
  = ·predℤ (pos (suc x)) (negsuc y) ∙
    cong (_- pos (suc x)) (·DistPosRMin (suc x) (negsuc y) (pos zero)) ∙
    +DistLMin (pos (suc x) · negsuc y) (pos (suc x) · pos zero) (- pos (suc x)) ∙
    cong₂ min (sym (·predℤ (pos (suc x)) (negsuc y)))
              (cong (_+ negsuc x) (·AnnihilR (pos (suc x))) ∙
               sym (pos0+ (negsuc x)) ∙
               ·Comm (negsuc zero) (pos (suc x)))
·DistPosRMin (suc x) (negsuc (suc y)) (negsuc (suc z))
  = ·predℤ (pos (suc x)) (min (negsuc y) (negsuc z)) ∙
    cong (_- pos (suc x)) (·DistPosRMin (suc x) (negsuc y) (negsuc z)) ∙
    +DistLMin (pos (suc x) · negsuc y) (pos (suc x) · negsuc z) (- pos (suc x)) ∙
    cong₂ min (sym (·predℤ (pos (suc x)) (negsuc y)))
              (sym (·predℤ (pos (suc x)) (negsuc z)))

·DistPosLMin : (x y : ℤ) (z : ℕ) → min x y · pos z ≡ min (x · pos z) (y · pos z)
·DistPosLMin y z x = ·Comm (min y z) (pos x) ∙
                     ·DistPosRMin x y z ∙
                     cong₂ min (·Comm (pos x) y)
                               (·Comm (pos x) z)

·DistPosRMax : (x : ℕ) (y z : ℤ) → pos x · max y z ≡ max (pos x · y) (pos x · z)
·DistPosRMax x y z
  = sym (-Involutive (pos x · max y z)) ∙
    cong -_ (-DistR· (pos x) (max y z) ∙
             cong (pos x ·_) (-DistMax y z) ∙
             ·DistPosRMin x (- y) (- z)) ∙
    -DistMin (pos x · - y) (pos x · - z) ∙
    cong₂ max (-DistR· (pos x) (- y) ∙
               cong (pos x ·_) (-Involutive y))
              (-DistR· (pos x) (- z) ∙
               cong (pos x ·_) (-Involutive z))

·DistPosLMax : (x y : ℤ) (z : ℕ) → max x y · pos z ≡ max (x · pos z) (y · pos z)
·DistPosLMax y z x = ·Comm (max y z) (pos x) ∙
                     ·DistPosRMax x y z ∙
                     cong₂ max (·Comm (pos x) y)
                               (·Comm (pos x) z)

·DistNegsucRMin : (x : ℕ) (y z : ℤ) → negsuc x · min y z ≡ max (negsuc x · y) (negsuc x · z)
·DistNegsucRMin x y z
  = -DistLR· (negsuc x) (min y z) ∙
    cong (pos (suc x) ·_) (-DistMin y z) ∙
    ·DistPosRMax (suc x) (- y) (- z) ∙
    cong₂ max (sym (-DistR· (pos (suc x)) y) ∙
               -DistL· (pos (suc x)) y)
              (sym (-DistR· (pos (suc x)) z) ∙
               -DistL· (pos (suc x)) z)

·DistNegsucLMin : (x y : ℤ) (z : ℕ) → min x y · negsuc z ≡ max (x · negsuc z) (y · negsuc z)
·DistNegsucLMin y z x = ·Comm (min y z) (negsuc x) ∙
                        ·DistNegsucRMin x y z ∙
                        cong₂ max (·Comm (negsuc x) y)
                                  (·Comm (negsuc x) z)

·DistNegsucRMax : (x : ℕ) (y z : ℤ) → negsuc x · max y z ≡ min (negsuc x · y) (negsuc x · z)
·DistNegsucRMax x y z
  = -DistLR· (negsuc x) (max y z) ∙
    cong (pos (suc x) ·_) (-DistMax y z) ∙
    ·DistPosRMin (suc x) (- y) (- z) ∙
    cong₂ min (sym (-DistR· (pos (suc x)) y) ∙
               -DistL· (pos (suc x)) y)
              (sym (-DistR· (pos (suc x)) z) ∙
               -DistL· (pos (suc x)) z)

·DistNegsucLMax : (x y : ℤ) (z : ℕ) → max x y · negsuc z ≡ min (x · negsuc z) (y · negsuc z)
·DistNegsucLMax y z x = ·Comm (max y z) (negsuc x) ∙
                        ·DistNegsucRMax x y z ∙
                        cong₂ min (·Comm (negsuc x) y)
                                  (·Comm (negsuc x) z)

minus≡0- : (x : ℤ) → - x ≡ (0 - x)
minus≡0- x = +Comm (- x) 0

-- Absolute values
abs→⊎ : (x : ℤ) (n : ℕ) → abs x ≡ n → (x ≡ pos n) ⊎ (x ≡ - pos n)
abs→⊎ x n = J (λ n _ → (x ≡ pos n) ⊎ (x ≡ - pos n)) (help x)
  where
  help : (x : ℤ) → (x ≡ pos (abs x)) ⊎ (x ≡ - pos (abs x))
  help (pos n) = inl refl
  help (negsuc n) = inr refl

⊎→abs : (x : ℤ) (n : ℕ) → (x ≡ pos n) ⊎ (x ≡ - pos n) → abs x ≡ n
⊎→abs (pos n₁) n (inl x₁) = cong abs x₁
⊎→abs (negsuc n₁) n (inl x₁) = cong abs x₁
⊎→abs x zero (inr x₁) = cong abs x₁
⊎→abs x (suc n) (inr x₁) = cong abs x₁

abs≡0 : (x : ℤ) → abs x ≡ 0 → x ≡ 0
abs≡0 x p =
  case (abs→⊎ x 0 p)
  return (λ _ → x ≡ 0) of
    λ { (inl r) → r
      ; (inr r) → r }

¬x≡0→¬abs≡0 : {x : ℤ} → ¬ x ≡ 0 → ¬ abs x ≡ 0
¬x≡0→¬abs≡0 p q = p (abs≡0 _ q)

abs- : (x : ℤ) → abs (- x) ≡ abs x
abs- (pos zero) = refl
abs- (pos (suc n)) = refl
abs- (negsuc n) = refl

absPos·Pos : (m n : ℕ) → abs (pos m · pos n) ≡ abs (pos m) ·ℕ abs (pos n)
absPos·Pos m n i = abs (pos·pos m n (~ i))

abs· : (m n : ℤ) → abs (m · n) ≡ abs m ·ℕ abs n
abs· (pos m) (pos n) = absPos·Pos m n
abs· (pos m) (negsuc n) =
  cong abs (pos·negsuc m n) ∙ abs- (pos m · pos (suc n)) ∙ absPos·Pos m (suc n)
abs· (negsuc m) (pos n) =
  cong abs (negsuc·pos m n) ∙ abs- (pos (suc m) · pos n) ∙ absPos·Pos (suc m) n
abs· (negsuc m) (negsuc n) = cong abs (negsuc·negsuc m n) ∙ absPos·Pos (suc m) (suc n)

-- ℤ is integral domain

isIntegralℤPosPos : (c m : ℕ) → pos c · pos m ≡ 0 → ¬ c ≡ 0 → m ≡ 0
isIntegralℤPosPos 0 m _ q = ⊥.rec (q refl)
isIntegralℤPosPos (suc c) m p _ =
  sym (0≡n·sm→0≡n {n = m} {m = c} (sym (injPos (pos·pos (suc c) m ∙ p)) ∙ ·ℕ-comm (suc c) m))

isIntegralℤ : (c m : ℤ) → c · m ≡ 0 → ¬ c ≡ 0 → m ≡ 0
isIntegralℤ (pos c) (pos m) p h i = pos (isIntegralℤPosPos c m p (λ r → h (cong pos r)) i)
isIntegralℤ (pos c) (negsuc m) p h =
  ⊥.rec (snotz (isIntegralℤPosPos c (suc m)
    (sym (-Involutive _) ∙ cong (-_) (sym (pos·negsuc c m) ∙ p)) (λ r → h (cong pos r))))
isIntegralℤ (negsuc c) (pos m) p _ i =
  pos (isIntegralℤPosPos (suc c) m
    (sym (-Involutive _) ∙ cong (-_) (sym (negsuc·pos c m) ∙ p)) snotz i)
isIntegralℤ (negsuc c) (negsuc m) p _ =
  ⊥.rec (snotz (isIntegralℤPosPos (suc c) (suc m) (sym (negsuc·negsuc c m) ∙ p) snotz))

private
  ·lCancel-helper : (c m n : ℤ) → c · m ≡ c · n → c · (m - n) ≡ 0
  ·lCancel-helper c m n p =
      ·DistR+ c m (- n)
    ∙ (λ i → c · m + -DistR· c n (~ i))
    ∙ subst (λ a → c · m - a ≡ 0) p (-Cancel (c · m))

·lCancel : (c m n : ℤ) → c · m ≡ c · n → ¬ c ≡ 0 → m ≡ n
·lCancel c m n p h = -≡0 _ _ (isIntegralℤ c (m - n) (·lCancel-helper c m n p) h)

·rCancel : (c m n : ℤ) → m · c ≡ n · c → ¬ c ≡ 0 → m ≡ n
·rCancel c m n p h = ·lCancel c m n (·Comm c m ∙ p ∙ ·Comm n c) h


-Cancel'' : ∀ z → z ≡ - z → z ≡ 0
-Cancel'' z r = isIntegralℤ 2 z
                (cong (λ X → z + X) r ∙ -Cancel z)
                λ r → ⊥.rec (snotz (injPos r))

-- ℤ is non-trivial

0≢1-ℤ : ¬ 0 ≡ 1
0≢1-ℤ p = encodeℕ _ _ (injPos p)

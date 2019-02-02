{-# OPTIONS --cubical --safe #-}
module Cubical.Data.Int.Properties where

open import Cubical.Core.Everything

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels

open import Cubical.Data.Empty
open import Cubical.Data.Nat hiding (_+_ ; +-assoc)
open import Cubical.Data.Sum
open import Cubical.Data.Int.Base

open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.DecidableEq

sucPred : ∀ i → sucInt (predInt i) ≡ i
sucPred (pos zero)       = refl
sucPred (pos (suc n))    = refl
sucPred (negsuc zero)    = refl
sucPred (negsuc (suc n)) = refl

predSuc : ∀ i → predInt (sucInt i) ≡ i
predSuc (pos zero)       = refl
predSuc (pos (suc n))    = refl
predSuc (negsuc zero)    = refl
predSuc (negsuc (suc n)) = refl

suc-equiv : Int ≃ Int
suc-equiv = (sucInt , isoToIsEquiv sucInt predInt sucPred predSuc)

sucPathInt : Int ≡ Int
sucPathInt = ua suc-equiv

-- Compose sucPathInt with itself n times. Transporting along this
-- will be addition, transporting with it backwards will be
-- subtraction.
addEq : ℕ → Int ≡ Int
addEq zero = refl
addEq (suc n) = compPath sucPathInt (addEq n)

subEq : ℕ → Int ≡ Int
subEq n i = addEq n (~ i)

_+_ : Int → Int → Int
m + pos n    = transport (addEq n) m
m + negsuc n = transport (subEq (suc n)) m

_-_ : Int → Int → Int
m - pos zero    = m
m - pos (suc n) = m + negsuc n
m - negsuc n    = m + pos (suc n)

-- We directly get that addition by a fixed number is an equivalence
-- without having to do any induction!
isEquivAddInt : (m : Int) → isEquiv (λ n → n + m)
isEquivAddInt (pos n)    = isEquivTransport (addEq n)
isEquivAddInt (negsuc n) = isEquivTransport (subEq (suc n))

-- TODO: prove properties of + like:
--
-- +-comm : ∀ m n → m + n ≡ n + m
-- +-assoc : ∀ m n o → m + (n + o) ≡ (m + n) + o
--
-- Note: This might be a lot easier with the Cubical.Data.Int.Rewrite


-- TODO: define multiplication by composing the addition equivalence
-- with itself.

private
  -- TODO: can we change this so that it's the proof suc-equiv?
  coherence : (n : Int) → Path (Path Int (sucInt (predInt (sucInt n))) (sucInt n))
                               (sucPred (sucInt n))
                               (cong sucInt (predSuc n))
  coherence (pos zero) = refl
  coherence (pos (suc n)) = refl
  coherence (negsuc zero) = refl
  coherence (negsuc (suc zero)) = refl
  coherence (negsuc (suc (suc n))) = refl

-- Some tests
private
  one : Int
  one = transport (λ i → sucPathInt i) (pos 0)

  onepath : one ≡ pos 1
  onepath = refl

  minusone : Int
  minusone = transport (λ i → sucPathInt (~ i)) (pos 0)

  minusonepath : minusone ≡ negsuc 0
  minusonepath = refl

injPos : ∀ {a b : ℕ} → pos a ≡ pos b → a ≡ b
injPos {a} h = subst T h refl
  where
  T : Int → Set
  T (pos x)    = a ≡ x
  T (negsuc _) = ⊥

injNegsuc : ∀ {a b : ℕ} → negsuc a ≡ negsuc b → a ≡ b
injNegsuc {a} h = subst T h refl
  where
  T : Int → Set
  T (pos _) = ⊥
  T (negsuc x) = a ≡ x

posNotnegsuc : ∀ (a b : ℕ) → ¬ (pos a ≡ negsuc b)
posNotnegsuc a b h = subst T h 0
  where
  T : Int → Set
  T (pos _)    = ℕ
  T (negsuc _) = ⊥

negsucNotpos : ∀ (a b : ℕ) → ¬ (negsuc a ≡ pos b)
negsucNotpos a b h = subst T h 0
  where
  T : Int → Set
  T (pos _)    = ⊥
  T (negsuc _) = ℕ

discreteInt : Discrete Int
discreteInt (pos n) (pos m) with discreteℕ n m
... | yes p = yes (cong pos p)
... | no p  = no (λ x → p (injPos x))
discreteInt (pos n) (negsuc m) = no (posNotnegsuc n m)
discreteInt (negsuc n) (pos m) = no (negsucNotpos n m)
discreteInt (negsuc n) (negsuc m) with discreteℕ n m
... | yes p = yes (cong negsuc p)
... | no p  = no (λ x → p (injNegsuc x))

isSetInt : isSet Int
isSetInt = Discrete→isSet discreteInt

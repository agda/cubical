{-# OPTIONS --cubical --rewriting #-}
module Cubical.Basics.Int where

open import Cubical.Core.Primitives
open import Cubical.Core.Prelude
open import Cubical.Core.Glue

open import Cubical.Basics.Empty
open import Cubical.Basics.IsoToEquiv
open import Cubical.Basics.Nat
open import Cubical.Basics.Hedberg

data Int : Set where
  pos    : (n : ℕ) → Int
  negsuc : (n : ℕ) → Int

sucℤ : Int → Int
sucℤ (pos n)          = pos (suc n)
sucℤ (negsuc zero)    = pos zero
sucℤ (negsuc (suc n)) = negsuc n

predℤ : Int → Int
predℤ (pos zero)    = negsuc zero
predℤ (pos (suc n)) = pos n
predℤ (negsuc n)    = negsuc (suc n)

sucPred : ∀ i → sucℤ (predℤ i) ≡ i
sucPred (pos zero)       = refl
sucPred (pos (suc n))    = refl
sucPred (negsuc zero)    = refl
sucPred (negsuc (suc n)) = refl

predSuc : ∀ i → predℤ (sucℤ i) ≡ i
predSuc (pos zero)       = refl
predSuc (pos (suc n))    = refl
predSuc (negsuc zero)    = refl
predSuc (negsuc (suc n)) = refl

suc-equiv : Int ≃ Int
suc-equiv .fst = sucℤ
suc-equiv .snd = isoToIsEquiv sucℤ predℤ sucPred predSuc

sucPathℤ : Int ≡ Int
sucPathℤ = ua suc-equiv

-- Some tests
module _ where
 private
  one : Int
  one = transp (λ i → sucPathℤ i) i0 (pos 0)

  onepath : one ≡ pos 1
  onepath = refl

  minusone : Int
  minusone = transp (λ i → sucPathℤ (~ i)) i0 (pos 0)

  minusonepath : minusone ≡ negsuc 0
  minusonepath = refl
  

-- The following should be removed once we have ghcomp and no empty systems!
{-# BUILTIN REWRITE _≡_ #-}

hcompIntEmpty : (n : Int) → hcomp (λ _ → empty) n ≡ n
hcompIntEmpty n i = hfill (λ _ → empty) (inc n) (~ i)

{-# REWRITE hcompIntEmpty #-}

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

discreteInt : discrete Int
discreteInt (pos n) (pos m) with discreteℕ n m
... | inl p = inl (cong pos p)
... | inr p = inr (λ x → p (injPos x))
discreteInt (pos n) (negsuc m) = inr (posNotnegsuc n m)
discreteInt (negsuc n) (pos m) = inr (negsucNotpos n m)
discreteInt (negsuc n) (negsuc m) with discreteℕ n m
... | inl p = inl (cong negsuc p)
... | inr p = inr (λ x → p (injNegsuc x))

isSetInt : isSet Int
isSetInt = discrete→isSet Int discreteInt

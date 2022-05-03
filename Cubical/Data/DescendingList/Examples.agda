------------------------------------------------------------------------
-- Descending lists
--
-- We present some simple examples to demonstrate
--
-- 1. the concatenation operation on sorted lists obtained by
--    transporting the one on finite multisets, and
--
-- 2. "sorting" finite multisets by converting into sorted lists.
------------------------------------------------------------------------

{-# OPTIONS --safe --experimental-lossy-unification #-}

module Cubical.Data.DescendingList.Examples where

open import Cubical.Foundations.Everything

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat

open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.DecidableEq

open import Cubical.HITs.FiniteMultiset


------------------------------------------------------------------------
-- The ordering relation on natural numbers
--
-- we work with the definition from the standard library.

infix 4 _≤_ _≥_

data _≤_ : ℕ → ℕ → Type where
 z≤n : ∀ {n}                 → zero  ≤ n
 s≤s : ∀ {m n} (m≤n : m ≤ n) → suc m ≤ suc n

_≥_ : ℕ → ℕ → Type
m ≥ n = n ≤ m

≤pred : {n m : ℕ} → suc n ≤ suc m → n ≤ m
≤pred (s≤s r) = r

≥isPropValued : {n m : ℕ} → isProp (n ≥ m)
≥isPropValued z≤n z≤n = refl
≥isPropValued (s≤s p) (s≤s q) = cong s≤s (≥isPropValued p q)

≥dec : (x y : ℕ) → Dec (x ≥ y)
≥dec zero zero = yes z≤n
≥dec zero (suc y) = no (λ ())
≥dec (suc x) zero = yes z≤n
≥dec (suc x) (suc y) with ≥dec x y
≥dec (suc x) (suc y) | yes p = yes (s≤s p)
≥dec (suc x) (suc y) | no ¬p = no (λ r → ¬p (≤pred r))

≰→≥ : {x y : ℕ} → ¬ (x ≥ y) → y ≥ x
≰→≥ {zero} {y} f = z≤n
≰→≥ {suc x} {zero} f = ⊥.rec (f z≤n)
≰→≥ {suc x} {suc y} f = s≤s (≰→≥ λ g → f (s≤s g))

≥trans : {x y z : ℕ} → x ≥ y → y ≥ z → x ≥ z
≥trans z≤n z≤n = z≤n
≥trans (s≤s r) z≤n = z≤n
≥trans (s≤s r) (s≤s s) = s≤s (≥trans r s)

≤≥→≡ : {x y : ℕ} → x ≥ y → y ≥ x → x ≡ y
≤≥→≡ z≤n z≤n = refl
≤≥→≡ (s≤s r) (s≤s s) = cong suc (≤≥→≡ r s)


open import Cubical.Data.DescendingList.Base ℕ _≥_
open import Cubical.Data.DescendingList.Properties ℕ _≥_
open isSetDL ≥isPropValued discreteℕ
open IsoToFMSet discreteℕ ≥dec ≥isPropValued ≥trans ≰→≥ ≤≥→≡

------------------------------------------------------------------------
-- A simple example of concatenating sorted lists

l1 : DL
l1 = cons 4 (cons 3 (cons 2 [] ≥ᴴ[]) (≥ᴴcons (s≤s (s≤s z≤n)))) (≥ᴴcons (s≤s (s≤s (s≤s z≤n))))

l2 : DL
l2 = cons 2 (cons 0 [] ≥ᴴ[]) (≥ᴴcons z≤n)

l3 : DL
l3 = l1 ++ᴰᴸ l2

ValueOfl3 : l3 ≡ cons 4 (cons 3 (cons 2 (cons 2 (cons 0 _ _) _) _) _) _
ValueOfl3 = refl

l3=l2++l1 : l3 ≡ l2 ++ᴰᴸ l1
l3=l2++l1 = refl

-- Commented as it was the slowest definition in the whole library :-)
-- LongerExample :   l1 ++ᴰᴸ l2 ++ᴰᴸ l1 ++ᴰᴸ l1 ++ᴰᴸ l2
--                 ≡ l2 ++ᴰᴸ l1 ++ᴰᴸ l2 ++ᴰᴸ l1 ++ᴰᴸ l1
-- LongerExample = refl


-- ------------------------------------------------------------------------
-- -- A simple example of sorting finite multisets

m1 : FMSet ℕ
m1 = 13 ∷ 9 ∷ 78 ∷ 31 ∷ 86 ∷ 3 ∷ 0 ∷ 99 ∷ []

m2 : FMSet ℕ
m2 = 3 ∷ 1 ∷ 4 ∷ 1 ∷ 5 ∷ 9 ∷ []

m3 : FMSet ℕ
m3 = toFMSet (toDL (m1 ++ m2))

ValueOfm3 :
        m3 ≡ 99 ∷ 86 ∷ 78 ∷ 31 ∷ 13 ∷ 9 ∷ 9 ∷ 5 ∷ 4 ∷ 3 ∷ 3 ∷ 1 ∷ 1 ∷ 0 ∷ []
ValueOfm3 = refl

ValueOfm1++m2 :
  m1 ++ m2 ≡ 13 ∷ 9 ∷ 78 ∷ 31 ∷ 86 ∷ 3 ∷ 0 ∷ 99 ∷ 3 ∷ 1 ∷ 4 ∷ 1 ∷ 5 ∷ 9 ∷ []
ValueOfm1++m2 = refl

m3=m1++m2 : m3 ≡ m1 ++ m2
m3=m1++m2 = toFMSet∘toDL≡id (m1 ++ m2)

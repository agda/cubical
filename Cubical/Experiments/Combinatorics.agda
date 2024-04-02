{-

Computable stuff constructed from the Combinatorics of Finite Sets

-}
{-# OPTIONS --safe #-}

module Cubical.Experiments.Combinatorics where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Bool
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.Data.Vec

open import Cubical.Data.SumFin renaming (Fin to Fin')
open import Cubical.Data.FinSet.Base
open import Cubical.Data.FinSet.Properties
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.FinSet.Cardinality
open import Cubical.Data.FinSet.DecidablePredicate
open import Cubical.Data.FinSet.Quotients

open import Cubical.HITs.PropositionalTruncation

open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.DecidablePropositions
  hiding (DecProp) renaming (DecProp' to DecProp)
open import Cubical.Relation.Binary

open import Cubical.Functions.Embedding
open import Cubical.Functions.Surjection

private
  variable
    ℓ ℓ' ℓ'' : Level

-- convenient renaming

Fin : ℕ → FinSet ℓ-zero
Fin n = _ , isFinSetFin {n = n}

-- explicit numbers

s2 : card (_ , isFinSet≃ (Fin 2) (Fin 2)) ≡ 2
s2 = refl

s3 : card (_ , isFinSet≃ (Fin 3) (Fin 3)) ≡ 6
s3 = refl

a3,2 : card (_ , isFinSet↪ (Fin 2) (Fin 3)) ≡ 6
a3,2 = refl

2^4 : card (_ , isFinSet→ (Fin 4) (Fin 2)) ≡ 16
2^4 = refl

-- construct numerical functions from list
getFun : {n : ℕ} → Vec ℕ n → Fin n .fst → ℕ
getFun {n = n} ns = fun n ns
  where
    fun : (n : ℕ) → Vec ℕ n → Fin' n → ℕ
    fun 0 _ _ = 0
    fun (suc m) (n ∷ ns) (inl tt) = n
    fun (suc m) (n ∷ ns) (inr x) = fun m ns x

-- an example function
f = getFun (3 ∷ 1 ∷ 4 ∷ 1 ∷ 5 ∷ 9 ∷ 2 ∷ 6 ∷ [])

-- the total sum
s : sum (Fin _) f ≡ 31
s = refl

-- the total product
p : prod (Fin _) f ≡ 6480
p = refl

{-
-- the maximal value
m : maxValue (Fin _) f ∣ fzero ∣ ≡ 9
m = refl
-}
-- the number of numeral 1
n1 : card (_ , isFinSetFiberDisc (Fin _) ℕ discreteℕ f 1) ≡ 2
n1 = refl

-- a somewhat trivial equivalence relation making everything equivalent
R : {n : ℕ} → Fin n .fst → Fin n .fst → Type
R _ _ = Unit

isDecR : {n : ℕ} → (x y : Fin n .fst) → isDecProp (R {n = n} x y)
isDecR _ _ = true , idEquiv _

open BinaryRelation
open isEquivRel

isEquivRelR : {n : ℕ} → isEquivRel (R {n = n})
isEquivRelR {n = n} .reflexive _ = tt
isEquivRelR {n = n} .symmetric _ _ tt = tt
isEquivRelR {n = n} .transitive _ _ _ tt tt = tt

collapsed : (n : ℕ) → FinSet ℓ-zero
collapsed n = _ , isFinSetQuot (Fin n) R isEquivRelR isDecR

-- this number should be 1
≡1 : card (collapsed 2) ≡ 1
≡1 = refl

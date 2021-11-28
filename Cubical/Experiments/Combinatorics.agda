{-

Computable stuff constructed from the Combinatorics of Finite Sets

-}
{-# OPTIONS --safe #-}

module Cubical.Experiments.Combinatorics where

open import Cubical.Foundations.Prelude renaming (_≡_ to _≡'_)
open import Cubical.Foundations.Equiv renaming (_≃_ to _≃'_)

open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Bool
open import Cubical.Data.Sum
open import Cubical.Data.Sigma renaming (_×_ to _×'_)
open import Cubical.Data.Vec

open import Cubical.Data.SumFin renaming (Fin to Fin')
open import Cubical.Data.FinSet.Base
open import Cubical.Data.FinSet.Properties
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.FinSet.Cardinality
open import Cubical.Data.FinSet.Decidability
open import Cubical.Data.FinSet.Quotients

open import Cubical.HITs.PropositionalTruncation renaming (∥_∥ to ∥_∥')

open import Cubical.Relation.Nullary renaming (¬_ to ¬'_ ; ∥_∥ to ∥_∥')
open import Cubical.Relation.Binary

open import Cubical.Functions.Embedding  renaming (_↪_ to _↪'_)
open import Cubical.Functions.Surjection renaming (_↠_ to _↠'_)

private
  variable
    ℓ ℓ' ℓ'' : Level

-- renaming of type constructors

_+_ : FinSet ℓ → FinSet ℓ' → FinSet (ℓ-max ℓ ℓ')
X + Y = _ , isFinSet⊎ X Y

_×_ : FinSet ℓ → FinSet ℓ' → FinSet (ℓ-max ℓ ℓ')
X × Y = _ , isFinSet× X Y

_⇒_ : FinSet ℓ → FinSet ℓ' → FinSet (ℓ-max ℓ ℓ')
X ⇒ Y = _ , isFinSet→ X Y

_≃_ : FinSet ℓ → FinSet ℓ' → FinSet (ℓ-max ℓ ℓ')
X ≃ Y = _ , isFinSet≃ X Y

_↪_ : FinSet ℓ → FinSet ℓ' → FinSet (ℓ-max ℓ ℓ')
X ↪ Y = _ , isFinSet↪ X Y

_↠_ : FinSet ℓ → FinSet ℓ' → FinSet (ℓ-max ℓ ℓ')
X ↠ Y = _ , isFinSet↠ X Y

𝝨 : (X : FinSet ℓ) → (Y : X .fst → FinSet ℓ') → FinSet (ℓ-max ℓ ℓ')
𝝨 X Y = _ , isFinSetΣ X Y

𝝥 : (X : FinSet ℓ) → (Y : X .fst → FinSet ℓ') → FinSet (ℓ-max ℓ ℓ')
𝝥 X Y = _ , isFinSetΠ X Y

≋ : (X : FinSet ℓ) → (a b : X .fst) → FinSet ℓ
≋ X a b = _ , isFinSet≡ X a b

¬_ : FinSet ℓ → FinSet ℓ
¬ X = _ , isFinSet¬ X

∥_∥ : FinSet ℓ → FinSet ℓ
∥ X ∥ = _ , isFinSet∥∥ X

Fin : ℕ → FinSet ℓ-zero
Fin n = _ , isFinSetFin {n = n}

-- some computable functions

-- this should be addition
Fin+ : ℕ → ℕ → ℕ
Fin+ m n = card (Fin m + Fin n)

-- this should be multiplication
Fin× : ℕ → ℕ → ℕ
Fin× m n = card (Fin m × Fin n)

-- this should be exponential
Fin⇒ : ℕ → ℕ → ℕ
Fin⇒ m n = card (Fin m ⇒ Fin n)

-- this should be factorial or zero
Fin≃ : ℕ → ℕ → ℕ
Fin≃ m n = card (Fin m ≃ Fin n)

-- this should be permutation number
Fin↪ : ℕ → ℕ → ℕ
Fin↪ m n = card (Fin m ↪ Fin n)

-- this should be something that I don't know the name
Fin↠ : ℕ → ℕ → ℕ
Fin↠ m n = card (Fin m ↠ Fin n)

-- explicit numbers

s2 : Fin≃ 2 2 ≡ 2
s2 = refl

s3 : Fin≃ 3 3 ≡ 6
s3 = refl

a3,2 : Fin↪ 2 3 ≡ 6
a3,2 = refl

2^4 : Fin⇒ 4 2 ≡ 16
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

-- the maximal value
m : maxValue (Fin _) f ∣ fzero ∣ ≡ 9
m = refl

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

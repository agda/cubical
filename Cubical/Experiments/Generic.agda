{-# OPTIONS --cubical --safe #-}
module Cubical.Experiments.Generic where

open import Agda.Builtin.String
open import Agda.Builtin.List
open import Agda.Builtin.Float

open import Cubical.Core.Primitives
open import Cubical.Core.Prelude
open import Cubical.Core.Glue

open import Cubical.Basics.Empty
open import Cubical.Basics.Equiv
open import Cubical.Basics.Nat
open import Cubical.Basics.NTypes
open import Cubical.Basics.Int
open import Cubical.Basics.Equiv
open import Cubical.Basics.Univalence

variable
  ℓ ℓ' : Level

swap : {A : Set ℓ} {B : Set ℓ'} → A × B → B × A
swap (x , y) = (y , x)
  
swapInv : {A : Set ℓ} {B : Set ℓ'} → (xy : A × B) → swap (swap xy) ≡ xy
swapInv xy = refl

isEquivSwap : (A : Set ℓ) (B : Set ℓ') → isEquiv (λ (xy : A × B) → swap xy)
isEquivSwap A B = isoToIsEquiv swap swap swapInv swapInv

swapEquiv : (A : Set ℓ) (B : Set ℓ') → A × B ≃ B × A
swapEquiv A B = (swap , isEquivSwap A B)

swapEq : (A : Set ℓ) (B : Set ℓ') → A × B ≡ B × A
swapEq A B = ua (swapEquiv A B)


-- First simple test:

test1 : List (ℕ × ℕ)
test1 = transp (λ i → List (swapEq ℕ ℕ i)) i0 ((1 , 2) ∷ [])

-- TODO: Running "C-c C-n test1" gives:
--
-- transp (λ i → Σ ℕ (λ _ → ℕ)) i0
--   (hcomp (λ i → empty)
--          (transp (λ i → Σ ℕ (λ _ → ℕ)) i0 (2 , 1)) ∷ []

-- This works:
test1refl : test1 ≡ ((2 , 1) ∷ [])
test1refl = refl

-- TODO: Why is the normalization producing such complicated output?


------------------------------------------------------------------------------
--
-- Dan Licata's example from slide 47 of:
-- http://dlicata.web.wesleyan.edu/pubs/l13jobtalk/l13jobtalk.pdf

There : Set → Set
There X = List (ℕ × String × (X × ℕ))

Database : Set
Database = There (ℕ × ℕ)

db : Database
db = (4  , "John"  , (30 ,  5) , 1956)
   ∷ (8  , "Hugo"  , (29 , 12) , 1978)
   ∷ (15 , "James" , (1  ,  7) , 1968)
   ∷ (16 , "Sayid" , (2  , 10) , 1967)   
   ∷ (23 , "Jack"  , (3  , 12) , 1969)
   ∷ (42 , "Sun"   , (20 ,  3) , 1980)   
   ∷ []

convert : Database → Database
convert d = transp (λ i → There (swapEq ℕ ℕ i)) i0 d

eu : Database
eu = convert db

-- TODO: Running "C-c C-n eu" produces some very complicated output

want : Database
want = (4  , "John"  , (5  , 30) , 1956)
     ∷ (8  , "Hugo"  , (12 , 29) , 1978)
     ∷ (15 , "James" , (7  ,  1) , 1968)
     ∷ (16 , "Sayid" , (10 ,  2) , 1967)   
     ∷ (23 , "Jack"  , (12 ,  3) , 1969)
     ∷ (42 , "Sun"   , (3  , 20) , 1980)   
     ∷ []

-- TODO: This is not proved by refl... Why??
-- test2 : eu ≡ want
-- test2 = {!!}

-- TODO: This is also not proved by refl:
-- test2 : db ≡ convert (convert db)
-- test2 = {!!}


------------------------------------------------------------------------------
--
-- Example inspired by:
--
-- Scrap Your Boilerplate: A Practical Design Pattern for Generic Programming
-- Ralf Lämmel & Simon Peyton Jones, TLDI'03

Address : Set
Address = String

Name : Set
Name = String

data Person : Set where
  P : Name → Address → Person

data Salary (A : Set) : Set where
  S : A → Salary A

data Employee (A : Set) : Set where
  E : Person → Salary A → Employee A

Manager : Set → Set
Manager A = Employee A

mutual
  data Dept (A : Set) : Set where
    D : Name → Manager A → List (SubUnit A) → Dept A

  data SubUnit (A : Set) : Set where
    PU : Employee A → SubUnit A
    DU : Dept A → SubUnit A

data Company (A : Set) : Set where
  C : List (Dept A) → Company A


-- Being the example

anders : Employee Int
anders = E (P "Anders" "Pittsburgh") (S (pos 2500))

andrea : Employee Int
andrea = E (P "Andrea" "Copenhagen") (S (pos 2000))

andreas : Employee Int
andreas = E (P "Andreas" "Gothenburg") (S (pos 3000))

-- For now we have a small company
genCom : Company Int
genCom =
  C ( D "Research" andreas (PU anders ∷ PU andrea ∷ [])
    ∷ [])

-- increase the salary for everyone by 1
incSalary : Company Int → Company Int
incSalary c = transp (λ i → Company (sucPathInt i)) i0 c

-- Increase everyone's salary with 1
genCom1 : Company Int
genCom1 = incSalary genCom

-- This works and gives us:
-- C (D (transp (λ i → String) i0 "Research")
--      (E (P "Andreas" "Gothenburg") (S (pos 3001)))
--   (PU (E (P "Anders" "Pittsburgh") (S (pos 2501))) ∷
--    PU (E (P "Andrea" "Copenhagen") (S (pos 2001))) ∷ [])
--   ∷ [])

-- TODO: why is transport for String not removed?


-- The following definition of addition is very cool! We directly get
-- that it's an equivalence.

-- Compose sucPathInt with itself n times. Transporting along this
-- will be addition, transporting with it backwards will be
-- subtraction.
addEq : ℕ → Int ≡ Int
addEq zero = refl
addEq (suc n) = compPath sucPathInt (addEq n)

subEq : ℕ → Int ≡ Int
subEq n i = addEq n (~ i)

addInt : Int → Int → Int
addInt m (pos n) = transp (λ i → addEq n i) i0 m
addInt m (negsuc n) = transp (λ i → subEq (suc n) i) i0 m

subInt : Int → Int → Int
subInt m (pos zero) = m
subInt m (pos (suc n)) = addInt m (negsuc n)
subInt m (negsuc n) = addInt m (pos (suc n))


-- Let's increase everyone's salary more!

incSalaryℕ : ℕ → Company Int → Company Int
incSalaryℕ n c = transp (λ i → Company (addEq n i)) i0 c

-- This is quite slow
genCom2 : Company Int
genCom2 = incSalaryℕ 2 genCom

-- This is very slow
genCom10 : Company Int
genCom10 = incSalaryℕ 10 genCom

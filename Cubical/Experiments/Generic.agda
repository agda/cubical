-- Two fun examples of generic programming using univalence

{-# OPTIONS --cubical --safe #-}
module Cubical.Experiments.Generic where

open import Agda.Builtin.String
open import Agda.Builtin.List

open import Cubical.Core.Everything

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence

open import Cubical.Data.Nat
open import Cubical.Data.Int
open import Cubical.Data.Prod

----------------------------------------------------------------------------
--
-- Dan Licata's example from slide 47 of:
-- http://dlicata.web.wesleyan.edu/pubs/l13jobtalk/l13jobtalk.pdf

There : Set → Set
There X = List (ℕ × String × (X × ℕ))

Database : Set
Database = There (ℕ × ℕ)

us : Database
us = (4  , "John"  , (30 ,  5) , 1956)
   ∷ (8  , "Hugo"  , (29 , 12) , 1978)
   ∷ (15 , "James" , (1  ,  7) , 1968)
   ∷ (16 , "Sayid" , (2  , 10) , 1967)
   ∷ (23 , "Jack"  , (3  , 12) , 1969)
   ∷ (42 , "Sun"   , (20 ,  3) , 1980)
   ∷ []

convert : Database → Database
convert d = transport (λ i → There (swapEq ℕ ℕ i)) d

-- Swap the dates of the American database to get the European format
eu : Database
eu = convert us

-- A sanity check
_ : us ≡ convert eu
_ = refl


----------------------------------------------------------------------------
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

-- First test of "mutual"
mutual
  data Dept (A : Set) : Set where
    D : Name → Manager A → List (SubUnit A) → Dept A

  data SubUnit (A : Set) : Set where
    PU : Employee A → SubUnit A
    DU : Dept A → SubUnit A

data Company (A : Set) : Set where
  C : List (Dept A) → Company A


-- A small example

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

-- Increase the salary for everyone by 1
incSalary : Company Int → Company Int
incSalary c = transport (λ i → Company (sucPathInt i)) c

genCom1 : Company Int
genCom1 = incSalary genCom


-- Increase the salary more
incSalaryℕ : ℕ → Company Int → Company Int
incSalaryℕ n c = transport (λ i → Company (addEq n i)) c

genCom2 : Company Int
genCom2 = incSalaryℕ 2 genCom

genCom10 : Company Int
genCom10 = incSalaryℕ 10 genCom

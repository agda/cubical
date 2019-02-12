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
-- open import Cubical.Data.Prod

variable
  ℓ ℓ' : Level

data _×_ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') : Set (ℓ-max ℓ ℓ') where
  _,_ : A → B → A × B

infixr 5 _×_

swap : {A : Set ℓ} {B : Set ℓ'} → A × B → B × A
swap (x , y) = (y , x)

swapInv : {A : Set ℓ} {B : Set ℓ'} → (xy : A × B) → swap (swap xy) ≡ xy
swapInv (_ , _) = refl

isEquivSwap : (A : Set ℓ) (B : Set ℓ') → isEquiv (λ (xy : A × B) → swap xy)
isEquivSwap A B = isoToIsEquiv swap swap swapInv swapInv

swapEquiv : (A : Set ℓ) (B : Set ℓ') → A × B ≃ B × A
swapEquiv A B = (swap , isEquivSwap A B)

swapEq : (A : Set ℓ) (B : Set ℓ') → A × B ≡ B × A
swapEq A B = ua (swapEquiv A B)

-- First simple test:

test1 : List (ℕ × ℕ)
test1 = transp (λ i → List (swapEq ℕ ℕ i)) i0 ((1 , 2) ∷ [])

test1refl : test1 ≡ ((2 , 1) ∷ [])
test1refl = refl

-- TODO: Why is the normalization producing such complicated output?

-- Answer: transp and hcomp are implemented negatively for record
-- types, so that's the normal form, normalization doesn't eta expand.

-- You can get a better normal form like this:

expand : ∀ {A : Set ℓ} {B : Set ℓ'} → A × B → A × B
expand (x , y) = (x , y)

map : ∀ {A : Set ℓ} {B : Set ℓ'} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

test1-5 : List (ℕ × ℕ)
test1-5 = map expand test1



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

eu_normal : Database
eu_normal =
       (4  , "John"  , (5  , 30) , 1956)
     ∷ (8  , "Hugo"  , (12 , 29) , 1978)
     ∷ (15 , "James" , (7  ,  1) , 1968)
     ∷ (16 , "Sayid" , (10 ,  2) , 1967)
     ∷ (23 , "Jack"  , (12 ,  3) , 1969)
     ∷ (42 , "Sun"   , (3  , 20) , 1980)
     ∷ []

test2 : eu ≡ eu_normal
test2 = refl


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

genCom1 : Company Int
genCom1 = incSalary genCom

-- The following definition of addition is very cool! We directly get
-- that it's an equivalence. I will upstream it later.

-- First define transport and prove that it is an equivalence

transport : ∀ {ℓ} {A B : Set ℓ} → A ≡ B → A → B
transport p a = transp (λ i → p i) i0 a

isEquivTransportRefl : ∀ {ℓ} (A : Set ℓ) → isEquiv (transport {ℓ} {A} {A} refl)
isEquivTransportRefl {ℓ} A = isoToIsEquiv (transport refl) (transport refl) rem rem
  where
  rem : (x : A) → transport refl (transport refl x) ≡ x
  rem x = compPath (cong (transport refl) (λ i → transp (λ _ → A) i x))
                   (λ i → transp (λ _ → A) i x)

isEquivTransport : ∀ {ℓ} {A B : Set ℓ} (p : A ≡ B) → isEquiv (transport p)
isEquivTransport {A = A} = J (λ y x → isEquiv (transport x)) (isEquivTransportRefl A)


-- Compose sucPathInt with itself n times. Transporting along this
-- will be addition, transporting with it backwards will be
-- subtraction.
addEq : ℕ → Int ≡ Int
addEq zero = refl
addEq (suc n) = compPath sucPathInt (addEq n)

subEq : ℕ → Int ≡ Int
subEq n i = addEq n (~ i)

addInt : Int → Int → Int
addInt m (pos n) = transport (addEq n) m
addInt m (negsuc n) = transport (subEq (suc n)) m

subInt : Int → Int → Int
subInt m (pos zero) = m
subInt m (pos (suc n)) = addInt m (negsuc n)
subInt m (negsuc n) = addInt m (pos (suc n))

-- We directly get that addition by a fixed number is an equivalence
-- without having to do any induction!
isEquivAddInt : (m : Int) → isEquiv (λ (n : Int) → addInt n m)
isEquivAddInt (pos n) = isEquivTransport (addEq n)
isEquivAddInt (negsuc n) = isEquivTransport (subEq (suc n))

-- Let's use this to increase everyone's salary more!

incSalaryℕ : ℕ → Company Int → Company Int
incSalaryℕ n c = transp (λ i → Company (addEq n i)) i0 c

genCom2 : Company Int
genCom2 = incSalaryℕ 2 genCom

genCom10 : Company Int
genCom10 = incSalaryℕ 10 genCom

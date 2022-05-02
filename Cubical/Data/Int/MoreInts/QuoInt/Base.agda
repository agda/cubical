-- Define the integers as a HIT by identifying +0 and -0
{-# OPTIONS --safe #-}
module Cubical.Data.Int.MoreInts.QuoInt.Base where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Relation.Nullary

open import Cubical.Data.Int using () renaming (ℤ to Int ; discreteℤ to discreteInt ; isSetℤ to isSetInt)
open import Cubical.Data.Nat as ℕ using (ℕ; zero; suc)
open import Cubical.Data.Bool as Bool using (Bool; not; notnot)

variable
  l : Level


Sign : Type₀
Sign = Bool

pattern spos = Bool.false
pattern sneg = Bool.true

_·S_ : Sign → Sign → Sign
_·S_ = Bool._⊕_


data ℤ : Type₀ where
  signed : (s : Sign) (n : ℕ) → ℤ
  posneg : signed spos 0 ≡ signed sneg 0

pattern pos n = signed spos n
pattern neg n = signed sneg n


sign : ℤ → Sign
sign (signed _ zero) = spos
sign (signed s (suc _)) = s
sign (posneg i) = spos

sign-pos : ∀ n → sign (pos n) ≡ spos
sign-pos zero = refl
sign-pos (suc n) = refl

abs : ℤ → ℕ
abs (signed _ n) = n
abs (posneg i) = zero

signed-inv : ∀ n → signed (sign n) (abs n) ≡ n
signed-inv (pos zero) = refl
signed-inv (neg zero) = posneg
signed-inv (signed s (suc n)) = refl
signed-inv (posneg i) j = posneg (i ∧ j)

signed-zero : ∀ s₁ s₂ → signed s₁ zero ≡ signed s₂ zero
signed-zero spos spos = refl
signed-zero sneg sneg = refl
signed-zero spos sneg = posneg
signed-zero sneg spos = sym posneg


rec : ∀ {A : Type l} → (pos' neg' : ℕ → A) → pos' 0 ≡ neg' 0 → ℤ → A
rec pos' neg' eq (pos m)    = pos' m
rec pos' neg' eq (neg m)    = neg' m
rec pos' neg' eq (posneg i) = eq i

elim : ∀ (P : ℤ → Type l)
       → (pos' : ∀ n → P (pos n))
       → (neg' : ∀ n → P (neg n))
       → (λ i → P (posneg i)) [ pos' 0 ≡ neg' 0 ]
       → ∀ z → P z
elim P pos' neg' eq (pos n) = pos' n
elim P pos' neg' eq (neg n) = neg' n
elim P pos' neg' eq (posneg i) = eq i


Int→ℤ : Int → ℤ
Int→ℤ (Int.pos n) = pos n
Int→ℤ (Int.negsuc n) = neg (suc n)

ℤ→Int : ℤ → Int
ℤ→Int (pos n) = Int.pos n
ℤ→Int (neg zero) = Int.pos 0
ℤ→Int (neg (suc n)) = Int.negsuc n
ℤ→Int (posneg _) = Int.pos 0

ℤ→Int→ℤ : ∀ (n : ℤ) → Int→ℤ (ℤ→Int n) ≡ n
ℤ→Int→ℤ (pos n) _       = pos n
ℤ→Int→ℤ (neg zero) i    = posneg i
ℤ→Int→ℤ (neg (suc n)) _ = neg (suc n)
ℤ→Int→ℤ (posneg j) i    = posneg (j ∧ i)

Int→ℤ→Int : ∀ (n : Int) → ℤ→Int (Int→ℤ n) ≡ n
Int→ℤ→Int (Int.pos n) _ = Int.pos n
Int→ℤ→Int (Int.negsuc n) _ = Int.negsuc n

Int≡ℤ : Int ≡ ℤ
Int≡ℤ = isoToPath (iso Int→ℤ ℤ→Int ℤ→Int→ℤ Int→ℤ→Int)

discreteℤ : Discrete ℤ
discreteℤ = subst Discrete Int≡ℤ discreteInt

isSetℤ : isSet ℤ
isSetℤ = subst isSet Int≡ℤ isSetInt


-_ : ℤ → ℤ
- signed s n = signed (not s) n
- posneg i   = posneg (~ i)

negate-invol : ∀ n → - - n ≡ n
negate-invol (signed s n) i = signed (notnot s i) n
negate-invol (posneg i)   _ = posneg i

negateEquiv : ℤ ≃ ℤ
negateEquiv = isoToEquiv (iso -_ -_ negate-invol negate-invol)

negateEq : ℤ ≡ ℤ
negateEq = ua negateEquiv


infixl 6 _+_
infixl 7 _·_

sucℤ : ℤ → ℤ
sucℤ (pos n)       = pos (suc n)
sucℤ (neg zero)    = pos 1
sucℤ (neg (suc n)) = neg n
sucℤ (posneg _)    = pos 1

predℤ : ℤ → ℤ
predℤ = subst (λ Z → (Z → Z)) negateEq sucℤ
  -- definitionally equal to λ n → - (sucℤ (- n))
  -- strictly more useful than the direct pattern matching version,
  --  see negateSuc and negatePred

sucPredℤ : ∀ n → sucℤ (predℤ n) ≡ n
sucPredℤ (pos zero)    = sym posneg
sucPredℤ (pos (suc _)) = refl
sucPredℤ (neg _)       = refl
sucPredℤ (posneg i) j  = posneg (i ∨ ~ j)

predSucℤ : ∀ n → predℤ (sucℤ n) ≡ n
predSucℤ (pos _)       = refl
predSucℤ (neg zero)    = posneg
predSucℤ (neg (suc _)) = refl
predSucℤ (posneg i) j  = posneg (i ∧ j)

_+_ : ℤ → ℤ → ℤ
(signed _ zero) + n = n
(posneg _)      + n = n
(pos (suc m))   + n = sucℤ  (pos m + n)
(neg (suc m))   + n = predℤ (neg m + n)


sucPathℤ : ℤ ≡ ℤ
sucPathℤ  = isoToPath (iso sucℤ predℤ sucPredℤ predSucℤ)

-- We do the same trick as in Cubical.Data.Int to prove that addition
-- is an equivalence
addEqℤ : ℕ → ℤ ≡ ℤ
addEqℤ zero    = refl
addEqℤ (suc n) = addEqℤ n ∙ sucPathℤ

predPathℤ : ℤ ≡ ℤ
predPathℤ = isoToPath (iso predℤ sucℤ predSucℤ sucPredℤ)

subEqℤ : ℕ → ℤ ≡ ℤ
subEqℤ zero    = refl
subEqℤ (suc n) = subEqℤ n ∙ predPathℤ

addℤ : ℤ → ℤ → ℤ
addℤ (pos m) n    = transport (addEqℤ m) n
addℤ (neg m) n    = transport (subEqℤ m) n
addℤ (posneg _) n = n

isEquivAddℤ : (m : ℤ) → isEquiv (addℤ m)
isEquivAddℤ (pos n)    = isEquivTransport (addEqℤ n)
isEquivAddℤ (neg n)    = isEquivTransport (subEqℤ n)
isEquivAddℤ (posneg _) = isEquivTransport refl

addℤ≡+ℤ : addℤ ≡ _+_
addℤ≡+ℤ i  (pos (suc m)) n = sucℤ   (addℤ≡+ℤ i (pos m) n)
addℤ≡+ℤ i  (neg (suc m)) n = predℤ  (addℤ≡+ℤ i (neg m) n)
addℤ≡+ℤ i  (pos zero) n    = n
addℤ≡+ℤ i  (neg zero) n    = n
addℤ≡+ℤ _  (posneg _) n    = n

isEquiv+ℤ : (m : ℤ) → isEquiv (m +_)
isEquiv+ℤ = subst (λ _+_ → (m : ℤ) → isEquiv (m +_)) addℤ≡+ℤ isEquivAddℤ


_·_ : ℤ → ℤ → ℤ
m · n = signed (sign m ·S sign n) (abs m ℕ.· abs n)

private
  ·-abs : ∀ m n → abs (m · n) ≡ abs m ℕ.· abs n
  ·-abs m n = refl


-- Natural number and negative integer literals for ℤ

open import Cubical.Data.Nat.Literals public

instance
  fromNatℤ : HasFromNat ℤ
  fromNatℤ = record { Constraint = λ _ → Unit ; fromNat = λ n → pos n }

instance
  fromNegℤ : HasFromNeg ℤ
  fromNegℤ = record { Constraint = λ _ → Unit ; fromNeg = λ n → neg n }

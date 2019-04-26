-- Define the integers as a HIT by identifying +0 and -0
{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.HitInt.Base where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Int
open import Cubical.Data.Nat

data ℤ : Type₀ where
  pos    : (n : ℕ) → ℤ
  neg    : (n : ℕ) → ℤ
  posneg : pos 0 ≡ neg 0

recℤ : ∀ {l} {A : Type l} → (pos' neg' : ℕ → A) → pos' 0 ≡ neg' 0 → ℤ → A
recℤ pos' neg' eq (pos m)    = pos' m
recℤ pos' neg' eq (neg m)    = neg' m
recℤ pos' neg' eq (posneg i) = eq i

indℤ : ∀ {l} (P : ℤ → Type l)
       → (pos' : ∀ n → P (pos n))
       → (neg' : ∀ n → P (neg n))
       → (λ i → P (posneg i)) [ pos' 0 ≡ neg' 0 ]
       → ∀ z → P z
indℤ P pos' neg' eq (pos n) = pos' n
indℤ P pos' neg' eq (neg n) = neg' n
indℤ P pos' neg' eq (posneg i) = eq i

Int→ℤ : Int → ℤ
Int→ℤ (pos n) = pos n
Int→ℤ (negsuc n) = neg (suc n)

ℤ→Int : ℤ → Int
ℤ→Int (pos n) = pos n
ℤ→Int (neg zero) = pos 0
ℤ→Int (neg (suc n)) = negsuc n
ℤ→Int (posneg _) = pos 0

ℤ→Int→ℤ : ∀ (n : ℤ) → Int→ℤ (ℤ→Int n) ≡ n
ℤ→Int→ℤ (pos n) _       = pos n
ℤ→Int→ℤ (neg zero) i    = posneg i
ℤ→Int→ℤ (neg (suc n)) _ = neg (suc n)
ℤ→Int→ℤ (posneg j) i    = posneg (j ∧ i)

Int→ℤ→Int : ∀ (n : Int) → ℤ→Int (Int→ℤ n) ≡ n
Int→ℤ→Int (pos n) _ = pos n
Int→ℤ→Int (negsuc n) _ = negsuc n

Int≡ℤ : Int ≡ ℤ
Int≡ℤ = isoToPath (iso Int→ℤ ℤ→Int ℤ→Int→ℤ Int→ℤ→Int)

isSetℤ : isSet ℤ
isSetℤ = subst isSet Int≡ℤ isSetInt

sucℤ : ℤ → ℤ
sucℤ (pos n)       = pos (suc n)
sucℤ (neg zero)    = pos 1
sucℤ (neg (suc n)) = neg n
sucℤ (posneg _)    = pos 1

predℤ : ℤ → ℤ
predℤ (pos zero)    = neg 1
predℤ (pos (suc n)) = pos n
predℤ (neg n)       = neg (suc n)
predℤ (posneg _)    = neg 1

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

_+ℤ_ : ℤ → ℤ → ℤ
m +ℤ (pos (suc n)) = sucℤ   (m +ℤ pos n)
m +ℤ (neg (suc n)) = predℤ  (m +ℤ neg n)
m +ℤ _             = m

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
addℤ m (pos n)    = transport (addEqℤ n) m
addℤ m (neg n)    = transport (subEqℤ n) m
addℤ m (posneg _) = m

isEquivAddℤ : (m : ℤ) → isEquiv (λ n → addℤ n m)
isEquivAddℤ (pos n)    = isEquivTransport (addEqℤ n)
isEquivAddℤ (neg n)    = isEquivTransport (subEqℤ n)
isEquivAddℤ (posneg _) = isEquivTransport refl

addℤ≡+ℤ : addℤ ≡ _+ℤ_
addℤ≡+ℤ i  m (pos (suc n)) = sucℤ   (addℤ≡+ℤ i m (pos n))
addℤ≡+ℤ i  m (neg (suc n)) = predℤ  (addℤ≡+ℤ i m (neg n))
addℤ≡+ℤ i  m (pos zero)    = m
addℤ≡+ℤ i  m (neg zero)    = m
addℤ≡+ℤ _  m (posneg _)    = m

isEquiv+ℤ : (m : ℤ) → isEquiv (λ n → n +ℤ m)
isEquiv+ℤ = subst (λ _+_ → (m : ℤ) → isEquiv (λ n → n + m)) addℤ≡+ℤ isEquivAddℤ




data Sign : Type₀ where
  pos neg : Sign

sign : ℤ → Sign
sign (pos n)       = pos
sign (neg 0)       = pos
sign (neg (suc n)) = neg
sign (posneg i)    = pos

abs : ℤ → ℕ
abs (pos n) = n
abs (neg n) = n
abs (posneg i) = 0

signed : Sign → ℕ → ℤ
signed Sign.pos n = pos n
signed Sign.neg n = neg n

signed-inv : ∀ z → signed (sign z) (abs z) ≡ z
signed-inv (pos n)       = refl
signed-inv (neg zero)    = posneg
signed-inv (neg (suc n)) = refl
signed-inv (posneg i)    = \ j → posneg (i ∧ j)
{-

 The square for   signed-inv (posneg i)


              posneg i
       --------------------->
       ^                     ^
       |                     |
 pos 0 |                     | posneg j
       |                     |
       |                     |
       |                     |
       ---------------------->
         = pos 0
         = signed Sign.pos 0
         signed (sign (posneg i))
                (abs (posneg i))
-}


-- * Multiplication

_*S_ : Sign → Sign → Sign
pos *S neg = neg
neg *S pos = neg
_   *S _   = pos

_*ℤ_ : ℤ → ℤ → ℤ
m *ℤ n = signed (sign m *S sign n) (abs m * abs n)

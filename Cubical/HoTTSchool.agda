{-

Cubical Agda demo given at HoTT 2019 summer school.

Documentation: https://agda.readthedocs.io/en/v2.6.0.1/language/cubical.html

Paper: http://www.cs.cmu.edu/~amoertbe/papers/cubicalagda.pdf

Library: https://github.com/agda/cubical (release v0.1 compiles on latest Agda release)

-}
{-# OPTIONS --cubical #-}
module Cubical.HoTTSchool where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything

open import Cubical.Data.Nat
open import Cubical.Data.Prod

-- Univalence: Cubical.Foundations.Univalence

-- Binary natural numbers: Cubical.Data.BinNat.BinNat


-- HITs:

-- Integers as ℕ + ℕ where "inl 0 = inr 0".

data ℤ : Set where
  pos : ℕ → ℤ
  neg : ℕ → ℤ
  posneg : pos 0 ≡ neg 0

sucℤ : ℤ → ℤ
sucℤ (pos x) = pos (suc x)
sucℤ (neg zero) = pos 1
sucℤ (neg (suc x)) = neg x
sucℤ (posneg i) = pos 1

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

predPathℤ : ℤ ≡ ℤ
predPathℤ = isoToPath (iso predℤ sucℤ predSucℤ sucPredℤ)

addEqℤ : ℕ → ℤ ≡ ℤ
addEqℤ zero    = refl
addEqℤ (suc n) = addEqℤ n ∙ sucPathℤ

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

-- For more results see: Cubical.HITs.Ints.QuoInt.Base


-- Circle

data S¹ : Type₀ where
  base : S¹
  loop : base ≡ base

helix : S¹ → Type₀
helix base     = ℤ
helix (loop i) = sucPathℤ i

ΩS¹ : Type₀
ΩS¹ = base ≡ base

winding : ΩS¹ → ℤ
winding p = subst helix p (pos zero)

-- winding refl
-- winding (loop ∙ loop)
-- winding (loop ∙ sym loop)

-- For more results: Cubical.HITs.S1.Base


-- We will now prove "Torus = S¹ × S¹"

data Torus : Type₀ where
  point : Torus
  line1 : point ≡ point
  line2 : point ≡ point
  square : PathP (λ i → line1 i ≡ line1 i) line2 line2
-- Path^i (Path Torus (line1 i) (line1 i)) line2 line2

t2c : Torus → S¹ × S¹
t2c point = ( base , base )
t2c (line1 i) = ( loop i , base )
t2c (line2 i) = ( base , loop i )
t2c (square i j) = ( loop i , loop j )

c2t : S¹ × S¹ → Torus
c2t (base   , base)   = point
c2t (loop i , base)   = line1 i
c2t (base   , loop j) = line2 j
c2t (loop i , loop j) = square i j

c2t-t2c : ∀ (t : Torus) → c2t (t2c t) ≡ t
c2t-t2c point = refl
c2t-t2c (line1 i) = refl
c2t-t2c (line2 i) = refl
c2t-t2c (square i j) = refl

t2c-c2t : ∀ (p : S¹ × S¹) → t2c (c2t p) ≡ p
t2c-c2t (base   , base)   = refl
t2c-c2t (base   , loop _) = refl
t2c-c2t (loop _ , base)   = refl
t2c-c2t (loop _ , loop _) = refl

Torus≡S¹×S¹ : Torus ≡ S¹ × S¹
Torus≡S¹×S¹ = isoToPath (iso t2c c2t t2c-c2t c2t-t2c)

-- For more results about the Torus see: Cubical.HITs.Torus.Base



{-

Other cool things:

S³ = S¹ * S¹ ≡ TotalHopf: Cubical.HITs.Join.Base and Cubical.HITs.Hopf

Brunerie number: Cubical.Experiments.Brunerie

-}

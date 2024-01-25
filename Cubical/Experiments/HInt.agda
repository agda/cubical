{-# OPTIONS --safe #-}
{-

Definition of the integers as a HIT inspired by slide 10 of (original
idea due to Paolo Capriotti):

http://www.cs.nott.ac.uk/~psztxa/talks/bonn18.pdf

Disclaimer: this definition is very hard to work with and I have not
been able to prove that it is equivalent to nat + nat or that it is a
set.

For a variation that relies on a different notion of equivalence
(without any 2-cell) and which seems easier to work with see:

https://github.com/RedPRL/redtt/blob/master/library/cool/biinv-int.red

It might be interesting to port that example one day.

-}
module Cubical.Experiments.HInt where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Int renaming (ℤ to Int; sucℤ to sucInt; predℤ to predInt; isSetℤ to isSetInt)
open import Cubical.Data.Nat

data ℤ : Type₀ where
  zero : ℤ
  suc  : ℤ → ℤ
  pred : ℤ → ℤ
  sucpred : (n : ℤ) → suc (pred n) ≡ n
  predsuc : (n : ℤ) → pred (suc n) ≡ n
  -- Coherence: could also be written "sucpred (suc n) ≡ cong (suc (predsuc n))"
  coh     : (n : ℤ) → Path (suc (pred (suc n)) ≡ suc n)
                           (sucpred (suc n))
                           (λ i → suc (predsuc n i))

-- This is equivalent to Int:
coherence : (n : Int) → Path (Path Int (sucInt (predInt (sucInt n))) (sucInt n))
                             (sucPred (sucInt n))
                             (cong sucInt (predSuc n))
coherence (pos zero) = refl
coherence (pos (suc n)) = refl
coherence (negsuc zero) = refl
coherence (negsuc (suc zero)) = refl
coherence (negsuc (suc (suc n))) = refl

ℤ→Int : ℤ → Int
ℤ→Int zero = pos 0
ℤ→Int (suc n) = sucInt (ℤ→Int n)
ℤ→Int (pred n) = predInt (ℤ→Int n)
ℤ→Int (sucpred n i) = sucPred (ℤ→Int n) i
ℤ→Int (predsuc n i) = predSuc (ℤ→Int n) i
ℤ→Int (coh n i j) = coherence (ℤ→Int n) i j

ℕ→ℤ : ℕ → ℤ
ℕ→ℤ zero = zero
ℕ→ℤ (suc n) = suc (ℕ→ℤ n)

negsucℕ→ℤ : ℕ → ℤ
negsucℕ→ℤ zero = pred zero
negsucℕ→ℤ (suc n) = pred (negsucℕ→ℤ n)

Int→ℤ : Int → ℤ
Int→ℤ (pos n) = ℕ→ℤ n
Int→ℤ (negsuc n) = negsucℕ→ℤ n

lem1 : ∀ n → Int→ℤ (sucInt n) ≡ suc (Int→ℤ n)
lem1 (pos n) = refl
lem1 (negsuc zero) = sym (sucpred zero)
lem1 (negsuc (suc n)) = sym (sucpred (negsucℕ→ℤ n))

lem2 : ∀ n → Int→ℤ (predInt n) ≡ pred (Int→ℤ n)
lem2 (pos zero) = refl
lem2 (pos (suc n)) = sym (predsuc (ℕ→ℤ n))
lem2 (negsuc n) = refl

-- I don't see how to fill these holes, especially the last one
{-
ℤ→Int→ℤ : ∀ (n : ℤ) → Int→ℤ (ℤ→Int n) ≡ n
ℤ→Int→ℤ zero = refl
ℤ→Int→ℤ (suc n) = (lem1 (ℤ→Int n)) ∙ (cong suc (ℤ→Int→ℤ n))
ℤ→Int→ℤ (pred n) = (lem2 (ℤ→Int n)) ∙ (cong pred (ℤ→Int→ℤ n))
ℤ→Int→ℤ (sucpred n i) = {!!}
ℤ→Int→ℤ (predsuc n i) = {!!}
ℤ→Int→ℤ (coh n i j) = {!!}
-}

Int→ℤ→Int : ∀ n → ℤ→Int (Int→ℤ n) ≡ n
Int→ℤ→Int (pos zero) = refl
Int→ℤ→Int (pos (suc n)) = cong sucInt (Int→ℤ→Int (pos n))
Int→ℤ→Int (negsuc zero) = refl
Int→ℤ→Int (negsuc (suc n)) = cong predInt (Int→ℤ→Int (negsuc n))
{-
Int≡ℤ : Int ≡ ℤ
Int≡ℤ = isoToPath (iso Int→ℤ ℤ→Int ℤ→Int→ℤ Int→ℤ→Int)

isSetℤ : isSet ℤ
isSetℤ = subst isSet Int≡ℤ isSetInt
-}

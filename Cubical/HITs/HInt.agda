{-

Definition of the integers as a HIT inspired by slide 10 of (original
idea due to Paolo Capriotti):

http://www.cs.nott.ac.uk/~psztxa/talks/bonn18.pdf

-}
{-# OPTIONS --cubical #-}
module Cubical.HITs.HInt where

open import Cubical.Core.Primitives
open import Cubical.Core.Prelude
open import Cubical.Core.Glue

open import Cubical.Basics.IsoToEquiv
open import Cubical.Basics.Int
open import Cubical.Basics.Nat

data ℤ : Set where
  zero : ℤ
  suc  : ℤ → ℤ
  pred : ℤ → ℤ
  sucpred : (n : ℤ) → suc (pred n) ≡ n
  predsuc : (n : ℤ) → pred (suc n) ≡ n
  -- Coherence: could also be written "sucpred (suc n) ≡ cong (suc (predsuc n))"
  coh     : (n : ℤ) → Path (Path ℤ (suc (pred (suc n))) (suc n))
                           (sucpred (suc n))
                           (λ i → suc (predsuc n i))

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
negsucℕ→ℤ (suc n) = pred (ℕ→ℤ n)

Int→ℤ : Int → ℤ
Int→ℤ (pos n) = ℕ→ℤ n
Int→ℤ (negsuc n) = negsucℕ→ℤ n

foo1 : ∀ n → Int→ℤ (ℤ→Int n) ≡ n
foo1 n = {!!}

foo2 : ∀ n → ℤ→Int (Int→ℤ n) ≡ n
foo2 (pos n) = {!!}
foo2 (negsuc n) = {!!}

predℤ : ℤ → ℤ
predℤ zero = pred zero
predℤ (suc n) = n
predℤ (pred n) = pred (pred n)
predℤ (sucpred zero i) = pred zero
predℤ (sucpred (suc n) i) = predsuc n i
predℤ (sucpred (pred n) i) = pred (pred n)
predℤ (sucpred (sucpred n j) i) = {!!}
predℤ (sucpred (predsuc n j) i) = {!!}
predℤ (sucpred (coh n j k) i) = {!!}
predℤ (predsuc n j) = {!!}
predℤ (coh n k l) = {!!}

predSucℤ : ∀ n → predℤ (suc n) ≡ n
predSucℤ n = refl

-- This definition amounts to saying that suc is an equivalence. Can
-- we set it up so that the coherence is exactly what we need?
-- isEquivSuc : isEquiv suc
-- isEquivSuc .equiv-proof y =
--  let ctr : fiber suc y
--      ctr = (pred y , sym (sucpred y))
--      prf : (f : fiber suc y) → ctr ≡ f
--      prf f i = compPath (cong pred (f .snd)) (predsuc (f .fst)) i
--              , {!!}
--  in ctr , prf


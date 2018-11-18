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

open import Cubical.Basics.Equiv
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

-- This is equivalent to Int:

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

ℤ→Int→ℤ : ∀ (n : ℤ) → Path ℤ (Int→ℤ (ℤ→Int n)) n
ℤ→Int→ℤ zero = refl
ℤ→Int→ℤ (suc n) = compPath (lem1 (ℤ→Int n)) (cong suc (ℤ→Int→ℤ n))
ℤ→Int→ℤ (pred n) = compPath (lem2 (ℤ→Int n)) (cong pred (ℤ→Int→ℤ n))
ℤ→Int→ℤ (sucpred n i) = {!!}
ℤ→Int→ℤ (predsuc n i) = {!!}
ℤ→Int→ℤ (coh n i j) = {!!}

Int→ℤ→Int : ∀ n → ℤ→Int (Int→ℤ n) ≡ n
Int→ℤ→Int (pos zero) = refl
Int→ℤ→Int (pos (suc n)) = cong sucInt (Int→ℤ→Int (pos n))
Int→ℤ→Int (negsuc zero) = refl
Int→ℤ→Int (negsuc (suc n)) = cong predInt (Int→ℤ→Int (negsuc n))

Int≡ℤ : Int ≡ ℤ
Int≡ℤ = isoToPath Int→ℤ ℤ→Int ℤ→Int→ℤ Int→ℤ→Int

isSetℤ : isSet ℤ
isSetℤ = subst isSet Int≡ℤ isSetInt 






-- random stuff below:

-- foo : ∀ (a b : ℤ) → ℤ→Int a ≡ ℤ→Int b → a ≡ b
-- foo a b h = {!!}
-- -- subst T h refl
-- --   where
-- --   T : Int → Set
-- --   T (pos x)    = a ≡ x
-- --   T (negsuc _) = ⊥


-- discreteℤ : discrete ℤ
-- discreteℤ x y with discreteInt (ℤ→Int x) (ℤ→Int y)
-- ... | inl p = inl (foo _ _ p)
-- ... | inr p = inr (λ q → p (cong ℤ→Int q))


-- discreteInt (pos n) (pos m) with discreteℕ n m
-- ... | inl p = inl (cong pos p)
-- ... | inr p = inr (λ x → p (injPos x))
-- discreteInt (pos n) (negsuc m) = inr (posNotnegsuc n m)
-- discreteInt (negsuc n) (pos m) = inr (negsucNotpos n m)
-- discreteInt (negsuc n) (negsuc m) with discreteℕ n m
-- ... | inl p = inl (cong negsuc p)
-- ... | inr p = inr (λ x → p (injNegsuc x))

-- isSetInt : isSet Int
-- isSetInt = discrete→isSet discreteInt



-- We should now be able to define a predecessor that computes nicely

-- predℤ : ℤ → ℤ
-- predℤ zero = pred zero
-- predℤ (suc n) = n
-- predℤ (pred n) = pred (pred n)
-- predℤ (sucpred n i) = {!!}
-- predℤ (predsuc n j) = {!!}
-- predℤ (coh n k l) = isSetℤ {!n!} n {!!} {!!} k l

-- predSucℤ : ∀ n → predℤ (suc n) ≡ n
-- predSucℤ n = refl

-- sucPredℤ : ∀ (n : ℤ) → suc (predℤ n) ≡ n
-- sucPredℤ zero = sucpred zero
-- sucPredℤ (suc n) = refl
-- sucPredℤ (pred n) = sucpred (pred n)
-- sucPredℤ (sucpred n i) = {!!}
-- sucPredℤ (predsuc n i) = {!!}
-- sucPredℤ (coh n i j) = {!!}


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

{-# OPTIONS --cubical #-}
module Cubical.Basics.Int where

-- TODO: upstream?
open import Agda.Builtin.Nat public
  using (zero; suc; _+_; _*_)
  renaming (Nat to ℕ)

open import Cubical.Core.Primitives
open import Cubical.Core.Prelude
open import Cubical.Core.Glue

open import Cubical.Basics.IsoToEquiv

data Int : Set where
  pos    : (n : ℕ) → Int
  negsuc : (n : ℕ) → Int

sucℤ : Int → Int
sucℤ (pos n)          = pos (suc n)
sucℤ (negsuc zero)    = pos zero
sucℤ (negsuc (suc n)) = negsuc n

predℤ : Int → Int
predℤ (pos zero)    = negsuc zero
predℤ (pos (suc n)) = pos n
predℤ (negsuc n)    = negsuc (suc n)

sucPred : ∀ i → sucℤ (predℤ i) ≡ i
sucPred (pos zero)       = refl
sucPred (pos (suc n))    = refl
sucPred (negsuc zero)    = refl
sucPred (negsuc (suc n)) = refl

predSuc : ∀ i → predℤ (sucℤ i) ≡ i
predSuc (pos zero)       = refl
predSuc (pos (suc n))    = refl
predSuc (negsuc zero)    = refl
predSuc (negsuc (suc n)) = refl

suc-equiv : Int ≃ Int
suc-equiv .fst = sucℤ
suc-equiv .snd = isoToEquiv sucℤ predℤ sucPred predSuc

sucPathℤ : Int ≡ Int
sucPathℤ = ua suc-equiv



-- These two examples trigger a bug:
-- An internal error has occurred. Please report this as a bug.
-- Location of the error: src/full/Agda/TypeChecking/Primitive.hs:933
one : Int
one = transp (λ i → sucPathℤ i) i0 (pos 0)

minusone : Int
minusone = transp (λ i → sucPathℤ (~ i)) i0 (pos 0)

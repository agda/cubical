{-# OPTIONS --cubical #-}
module Cubical.HITs.HitInt where

open import Cubical.Core.Primitives
open import Cubical.Core.Prelude
open import Cubical.Core.Glue

open import Cubical.Basics.Equiv
open import Cubical.Basics.Int
open import Cubical.Basics.Nat

data HitInt : Set where
  pos : (n : ℕ) → HitInt
  neg : (n : ℕ) → HitInt
  posneg : pos 0 ≡ neg 0

Int→HitInt : Int → HitInt
Int→HitInt (pos n) = pos n
Int→HitInt (negsuc n) = neg (suc n)

HitInt→Int : HitInt → Int
HitInt→Int (pos n) = pos n
HitInt→Int (neg zero) = pos 0
HitInt→Int (neg (suc n)) = negsuc n
HitInt→Int (posneg _) = pos 0

HitInt→Int→HitInt : ∀ n → Int→HitInt (HitInt→Int n) ≡ n
HitInt→Int→HitInt (pos n) _ = pos n
HitInt→Int→HitInt (neg zero) i = posneg i
HitInt→Int→HitInt (neg (suc n)) _ = neg (suc n)
HitInt→Int→HitInt (posneg j) i = posneg (j ∧ i)

Int→HitInt→Int : ∀ n → HitInt→Int (Int→HitInt n) ≡ n
Int→HitInt→Int (pos n) _ = pos n
Int→HitInt→Int (negsuc n) _ = negsuc n

Int≡HitInt : Int ≡ HitInt
Int≡HitInt = isoToPath Int→HitInt HitInt→Int HitInt→Int→HitInt Int→HitInt→Int

isSetHitInt : isSet HitInt
isSetHitInt = subst isSet Int≡HitInt isSetInt

sucHitInt : HitInt → HitInt
sucHitInt (pos n) = pos (suc n)
sucHitInt (neg zero) = pos 1
sucHitInt (neg (suc n)) = neg n
sucHitInt (posneg _) = pos 1

predHitInt : HitInt → HitInt
predHitInt (pos zero) = neg 1
predHitInt (pos (suc n)) = pos n
predHitInt (neg n) = neg (suc n)
predHitInt (posneg _) = neg 1

sucPredHitInt : ∀ n → sucHitInt (predHitInt n) ≡ n
sucPredHitInt (pos zero) = sym posneg
sucPredHitInt (pos (suc _)) = refl
sucPredHitInt (neg _) = refl
sucPredHitInt (posneg x) = sym λ y → posneg (x ∨ y)

predSucHitInt : ∀ n → predHitInt (sucHitInt n) ≡ n
predSucHitInt (pos _) = refl
predSucHitInt (neg zero) = posneg
predSucHitInt (neg (suc _)) = refl
predSucHitInt (posneg x) y = posneg (y ∧ x)


{-
CW structure on suspensions
-}

module Cubical.CW.Instances.Susp where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat

open import Cubical.HITs.Pushout
open import Cubical.HITs.Susp

open import Cubical.CW.Base
open import Cubical.CW.Instances.Pushout
open import Cubical.CW.Instances.Empty
open import Cubical.CW.Instances.Unit

-- todo: explicit construction of arbitrary suspensions

-- Suspensions of finite CW complexes
isFinCWSusp : (A : finCW ℓ-zero) → isFinCW (Susp (fst A))
isFinCWSusp A =
  subst isFinCW PushoutSusp≡Susp
    (isFinCWPushout A finCWUnit finCWUnit _ _)

-- Iterated suspensions of finite CW complexes
isFinCWSusp^' : (A : finCW ℓ-zero) (n : ℕ) → isFinCW (Susp^' n (fst A))
isFinCWSusp^' A zero = snd A
isFinCWSusp^' A (suc n) = isFinCWSusp (_ , isFinCWSusp^' A n)

isFinCWSusp^ : (A : finCW ℓ-zero) (n : ℕ) → isFinCW (Susp^ n (fst A))
isFinCWSusp^ A n = subst isFinCW (Susp^'≡Susp^ n) (isFinCWSusp^' A n)

{-# OPTIONS --safe #-}
module Cubical.Algebra.CommRing.RadicalIdeal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
open import Cubical.Data.FinData hiding (elim)
open import Cubical.Data.Nat renaming ( _+_ to _+ℕ_ ; _·_ to _·ℕ_
                                      ; +-comm to +ℕ-comm
                                      ; ·-assoc to ·ℕ-assoc ; ·-comm to ·ℕ-comm
                                      ; _choose_ to _ℕchoose_ ; snotz to ℕsnotz)
open import Cubical.Data.Nat.Order

open import Cubical.HITs.PropositionalTruncation

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Ideal
open import Cubical.Algebra.CommRing.BinomialThm
open import Cubical.Algebra.Ring.QuotientRing
open import Cubical.Algebra.Ring.Properties
open import Cubical.Algebra.Ring.BigOps
open import Cubical.Algebra.RingSolver.ReflectionSolving hiding (∣)

private
  variable
    ℓ : Level

module _ (R' : CommRing ℓ) where
 private R = fst R'
 open CommRingStr (snd R')
 open RingTheory (CommRing→Ring R')
 open CommRingTheory R'
 open Exponentiation R'
 open BinomialThm R'
 open isCommIdeal

 -- is there a sqrt character?
 rad : ℙ R → ℙ R
 rad I x = (∃[ n ∈ ℕ ] x ^ n ∈ I) , propTruncIsProp

 radOfIdealIsIdeal : ∀ (I : ℙ R) → isCommIdeal R' I → isCommIdeal R' (rad I)
 +Closed (radOfIdealIsIdeal I ici) =
         map2 λ { (n , xⁿ∈I) (m , yᵐ∈I) → (n +ℕ m) , subst (_∈ I)
                                          (sym (BinomialThm (n +ℕ m) _ _))
                                          (∑Closed R' (I , ici) (BinomialVec (n +ℕ m) _ _)
                                            λ i → {!!}) }
  -- where
  -- +ClosedΣ
 contains0 (radOfIdealIsIdeal I ici) =
           ∣ 1 , subst (_∈ I) (sym (0LeftAnnihilates 1r)) (ici .contains0) ∣
 ·Closed (radOfIdealIsIdeal I ici) r =
         map λ { (n , xⁿ∈I) → n , subst (_∈ I) (sym (^-ldist-· r _ n)) (ici .·Closed (r ^ n) xⁿ∈I) }

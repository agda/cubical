{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.CommRing.GeneratedIdeal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
open import Cubical.Data.Vec
open import Cubical.Data.Nat using (ℕ)

open import Cubical.HITs.PropositionalTruncation

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring
open import Cubical.Algebra.Ring.Ideal
open import Cubical.Algebra.Ring.QuotientRing
open import Cubical.Algebra.RingSolver.CommRingSolver hiding (∣)

private
  variable
    ℓ : Level

module _ (Ring@(R , str) : CommRing {ℓ}) (r : R) where
  infixr 5 _holds
  _holds : hProp ℓ → Type ℓ
  P holds = fst P
  open CommRingStr str
  isSetR = isSetCommRing (R , str)
  R′ = CommRing→Ring (R , str)

  linearCombination : {n : ℕ} → Vec R n → Vec R n → R
  linearCombination [] [] = 0r
  linearCombination (c ∷ coefficients) (x ∷ l) = c · x + linearCombination coefficients l

  coefficientSum : {n : ℕ} → Vec R n → Vec R n → Vec R n
  coefficientSum [] [] = []
  coefficientSum (x ∷ c) (y ∷ c′) = x + y ∷ coefficientSum c c′

  sumHom+ : (n : ℕ) (c c′ l : Vec R n)
            → linearCombination (coefficientSum c c′) l
              ≡ linearCombination c l + linearCombination c′ l
  sumHom+ ℕ.zero [] [] [] = 0r ≡⟨ solution ⟩ 0r + 0r ∎
                            where
                              solution : 0r ≡ 0r + 0r
                              solution = solve Ring
  sumHom+ (ℕ.suc n) c c′ l = {!!}

  isLinearCombination : {n : ℕ} → Vec R n → R → hProp _
  isLinearCombination l x =
    ∥ Σ[ coefficients ∈ Vec R _ ] x ≡ linearCombination coefficients l ∥ ,
       propTruncIsProp

  {- If x and y are linear combinations of l, then (x + y) is
     a linear combination. -}
  isLinearCombination+ : {n : ℕ} {x y : R} → (l : Vec R n)
                         → isLinearCombination l x holds
                         → isLinearCombination l y holds
                         → isLinearCombination l (x + y) holds
  isLinearCombination+ l =
    elim (λ _ → isOfHLevelΠ 1 (λ _ → propTruncIsProp))
         (λ {(cx , px) → elim (λ _ → propTruncIsProp)
          λ {(cy , py) → ∣  coefficientSum cx cy , {!!} ∣}})

  {- If x is a linear combinations of l, then -x is
     a linear combination. -}
  isLinearCombination- : {n : ℕ} {x y : R} → (l : Vec R n)
                         → isLinearCombination l x holds
                         → isLinearCombination l (- x) holds
  isLinearCombination- l xIsLinearCombination = {!!}

{-
   generatedIdeal : {n : ℕ} → Vec R n → IdealsIn R′
   generatedIdeal l = (linearDependent l) ,
                      record
                        { +-closed = {!!}
                        ; -closed = {!!}
                        ; 0r-closed = {!!}
                        ; ·-closedLeft = {!!}
                        ; ·-closedRight = {!!}
                        }
-}

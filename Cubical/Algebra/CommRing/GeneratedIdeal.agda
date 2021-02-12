{-
  Define finitely generated ideals of commutative rings and
  show that they are an ideal.
  Parts of this should be reusable for explicit constructions
  of free modules over a finite set.
-}
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.CommRing.GeneratedIdeal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
open import Cubical.Data.Vec
open import Cubical.Data.Nat using (ℕ)

open import Cubical.HITs.PropositionalTruncation hiding (map)

open import Cubical.Algebra.CommRing.Base
open import Cubical.Algebra.Ring
open import Cubical.Algebra.Ring.Ideal
open import Cubical.Algebra.Ring.QuotientRing
open import Cubical.Algebra.RingSolver.ReflectionSolving hiding (∣)

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

  sumDist+ : (n : ℕ) (c c′ l : Vec R n)
            → linearCombination (coefficientSum c c′) l
              ≡ linearCombination c l + linearCombination c′ l
  sumDist+ ℕ.zero [] [] [] = solve Ring
  sumDist+ (ℕ.suc n) (x ∷ c) (y ∷ c′) (a ∷ l) =
    linearCombination (coefficientSum (x ∷ c) (y ∷ c′)) (a ∷ l)            ≡⟨ refl ⟩
    (x + y) · a + linearCombination (coefficientSum c c′) l                ≡⟨ step1 ⟩
    (x + y) · a + (linearCombination c l + linearCombination c′ l)         ≡⟨ step2 ⟩
    (x · a + linearCombination c l) + (y · a + linearCombination c′ l)     ≡⟨ refl ⟩
    linearCombination (x ∷ c) (a ∷ l) + linearCombination (y ∷ c′) (a ∷ l) ∎
    where
      step1 = cong (λ z → (x + y) · a + z) (sumDist+ n c c′ l)
      autoSolve : (x y a t1 t2 : R)
                  → (x + y) · a + (t1 + t2) ≡ (x · a + t1) + (y · a + t2)
      autoSolve = solve Ring
      step2 = autoSolve x y a _ _

  dist- : (n : ℕ) (c l : Vec R n)
          → linearCombination (map -_ c) l
            ≡ - linearCombination c l
  dist- ℕ.zero [] [] = solve Ring
  dist- (ℕ.suc n) (x ∷ c) (a ∷ l) =
      - x · a + linearCombination (map -_ c) l    ≡[ i ]⟨ - x · a + dist- n c l i ⟩
      - x · a - linearCombination c l             ≡⟨ step1 x a _ ⟩
      - (x · a + linearCombination c l)           ∎
      where step1 : (x a t1 : R) → - x · a - t1 ≡ - (x · a + t1)
            step1 = solve Ring

  dist0 : (n : ℕ) (l : Vec R n)
          → linearCombination (replicate 0r) l ≡ 0r
  dist0 ℕ.zero [] = refl
  dist0 (ℕ.suc n) (a ∷ l) =
    0r · a + linearCombination (replicate 0r) l ≡[ i ]⟨  0r · a + dist0 n l i ⟩
    0r · a + 0r                                 ≡⟨ step1 a ⟩
    0r ∎
    where step1 : (a : R) → 0r · a + 0r ≡ 0r
          step1 = solve Ring

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
          λ {(cy , py) →
            ∣  coefficientSum cx cy ,
                (_ + _                                           ≡[ i ]⟨ px i + py i ⟩
                 linearCombination cx l + linearCombination cy l ≡⟨ sym (sumDist+ _ cx cy l) ⟩
                 linearCombination (coefficientSum cx cy) l ∎) ∣}})

  {- If x is a linear combinations of l, then -x is
     a linear combination. -}
  isLinearCombination- : {n : ℕ} {x y : R} (l : Vec R n)
                         → isLinearCombination l x holds
                         → isLinearCombination l (- x) holds
  isLinearCombination- l =
    elim (λ _ → propTruncIsProp)
         λ {(cx , px) → ∣ map -_ cx ,
                         ( - _                             ≡⟨ cong -_ px ⟩
                           - linearCombination cx l        ≡⟨ sym (dist- _ cx l) ⟩
                           linearCombination (map -_ cx) l ∎) ∣}

  {- 0r is the trivial linear Combination -}
  isLinearCombination0 : {n : ℕ} (l : Vec R n)
                        → isLinearCombination l 0r holds
  isLinearCombination0 l = ∣ replicate 0r , sym (dist0 _ l) ∣

{-
   generatedIdeal : {n : ℕ} → Vec R n → IdealsIn R′
   generatedIdeal l = (isLinearCombination l) ,
                      record
                        { +-closed = {!!}
                        ; -closed = {!!}
                        ; 0r-closed = {!!}
                        ; ·-closedLeft = {!!}
                        ; ·-closedRight = {!!}
                        }
-}

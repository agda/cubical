module Cubical.Algebra.Polynomials.UnivariateList.KaratsubaTest where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat renaming ( _+_ to _+ℕ_ ; _·_ to _·ℕ_ ; _^_ to _^ℕ_
                                      ; ·-assoc to ·ℕ-assoc ; ·-comm to ·ℕ-comm) hiding (elim)
open import Cubical.Data.Bool

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.BoolCommRing
open import Cubical.Algebra.CommRing.Instances.Polynomials.UnivariatePolyList

open import Cubical.Algebra.Polynomials.UnivariateList.Base
open import Cubical.Algebra.Polynomials.UnivariateList.Karatsuba public

open PolyMod BoolCommRing
open CommRingStr (snd (UnivariatePolyList BoolCommRing))

module Defs where
  𝔽₂[X] = Poly BoolCommRing
  -- the test polynomial
  t : ℕ → 𝔽₂[X]
  t zero = []
  t (suc n) = true ∷ t n

  t²fast : ℕ → 𝔽₂[X]
  t²fast n = karatsuba BoolCommRing (t n) (t n)

  t²fast' : ℕ → 𝔽₂[X]
  t²fast' n = karatsuba' BoolCommRing (t n) (t n)

  t²slow : ℕ → 𝔽₂[X]
  t²slow n = (t n) · (t n)

  -- this is done for algebras normally
  eval : 𝔽₂[X] → Bool → Bool
  eval [] x = false
  eval (a ∷ p) x = a ⊕ (x and eval p x)
  eval (drop0 i) false = false
  eval (drop0 i) true = false

open Defs public

module fast-tests where

  -- fastTest100 : eval (t²fast' 100) true ≡ false
  -- fastTest100 = refl

  -- fastTest200 : eval (t²fast' 200) true ≡ false
  -- fastTest200 = refl

  -- fastTest300 : eval (t²fast 300) true ≡ false
  -- fastTest300 = refl

  -- fastTest400 : eval (t²fast 400) true ≡ false
  -- fastTest400 = refl

  -- fastTest500 : eval (t²fast 500) true ≡ false
  -- fastTest500 = refl

  -- fastTest600 : eval (t²fast 600) true ≡ false
  -- fastTest600 = refl

  -- fastTest700 : eval (t²fast 700) true ≡ false
  -- fastTest700 = refl

  -- fastTest800 : eval (t²fast 800) true ≡ false
  -- fastTest800 = refl

  -- fastTest900 : eval (t²fast 900) true ≡ false
  -- fastTest900 = refl

  -- fastTest1000 : eval (t²fast 1000) true ≡ false
  -- fastTest1000 = refl


module slow-tests where

  -- slowTest100 : eval (t²slow 100) true ≡ false
  -- slowTest100 = refl

  -- slowTest200 : eval (t²slow 200) true ≡ false
  -- slowTest200 = refl

  -- slowTest300 : eval (t²slow 300) true ≡ false
  -- slowTest300 = refl

  -- slowTest400 : eval (t²slow 400) true ≡ false
  -- slowTest400 = refl

  -- slowTest500 : eval (t²slow 500) true ≡ false
  -- slowTest500 = refl

  -- slowTest600 : eval (t²slow 600) true ≡ false
  -- slowTest600 = refl

  -- slowTest700 : eval (t²slow 700) true ≡ false
  -- slowTest700 = refl

  -- slowTest800 : eval (t²slow 800) true ≡ false
  -- slowTest800 = refl

  -- slowTest900 : eval (t²slow 900) true ≡ false
  -- slowTest900 = refl

  -- slowTest1000 : eval (t²slow 1000) true ≡ false
  -- slowTest1000 = refl

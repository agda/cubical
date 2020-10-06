{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.HITs.James.Base where

open import Cubical.Foundations.Everything renaming (J to J')
open import Cubical.HITs.S1
open import Cubical.HITs.Truncation.FromNegOne

private
  variable
    ℓ : Level
    A B : Type ℓ
    A∙ : Pointed ℓ

data J (A : Pointed ℓ) : Type ℓ where
  εJ : J A
  αJ : typ A → J A → J A
  δJ : (x : J A) → x ≡ αJ (pt A) x

test : J (S¹ , base) → hLevelTrunc 2 S¹
test εJ = ∣ base ∣
test (αJ base x) = test x
test (αJ (loop i) εJ) = ∣ loop i ∣
test (αJ (loop i) (αJ base y)) = test (αJ (loop i) y)
test (αJ (loop i) (αJ (loop j) y)) =  {! SquareHelp i j !} 
  where
  SquareHelp : Square (λ j → test (αJ (loop j) y)) (λ j → test (αJ (loop j) y))
                      (λ j → test (αJ (loop j) y)) λ j → test (αJ (loop j) y)
  SquareHelp = isSet→isSet' (isOfHLevelTrunc 2) _ _ _ _
test (αJ (loop i) (δJ y i₁)) = test (αJ (loop i) y)
test (δJ x i) = test x

{-
  Fiber as a pointed type
-}
{-# OPTIONS --safe #-}
module Cubical.Foundations.Pointed.Fiber where

open import Cubical.Foundations.Pointed.Base
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

private
  variable
    ℓ : Level

fiber∙ : {A B : Pointed ℓ} → (f : A →∙ B) → Pointed ℓ
fiber∙ {A = A} {B = B} f = fiber (fst f) (snd B) , snd A , snd f

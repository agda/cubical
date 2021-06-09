{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.Ring.Morphism where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.Ring

private
  variable
    ℓ : Level

identity : (R : Ring ℓ) → RingHom R R
identity R = (λ x → x) , (record
                            { pres0 = refl ; pres1 = refl ; pres+ = λ _ _ → refl ; pres· = λ _ _ → refl ; pres- = λ _ → refl })

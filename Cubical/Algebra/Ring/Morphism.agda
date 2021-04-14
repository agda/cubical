{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.Ring.Morphism where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.Ring

private
  variable
    ℓ : Level

identity : (R : Ring {ℓ}) → RingHom R R
identity R = ringhom (λ x → x) refl (λ _ _ → refl) λ _ _ → refl

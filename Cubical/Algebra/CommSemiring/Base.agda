{-# OPTIONS --safe #-}
module Cubical.Algebra.CommSemiring.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.SIP using (TypeWithStr)

open import Cubical.Algebra.CommMonoid
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Semiring.Base

private
  variable
    ℓ ℓ' : Level

record IsCommSemiring {R : Type ℓ}
                  (0r 1r : R) (_+_ _·_ : R → R → R) : Type ℓ where

  field
    isSemiring : IsSemiring 0r 1r _+_ _·_
    ·Comm : (x y : R) → x · y ≡ y · x

  open IsSemiring isSemiring public

record CommSemiringStr (A : Type ℓ) : Type (ℓ-suc ℓ) where

  field
    0r      : A
    1r      : A
    _+_     : A → A → A
    _·_     : A → A → A
    isCommSemiring  : IsCommSemiring 0r 1r _+_ _·_

  infixl 7 _·_
  infixl 6 _+_

  open IsCommSemiring isCommSemiring public

CommSemiring : ∀ ℓ → Type (ℓ-suc ℓ)
CommSemiring ℓ = TypeWithStr ℓ CommSemiringStr

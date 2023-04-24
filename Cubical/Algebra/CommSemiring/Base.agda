{-# OPTIONS --safe #-}
module Cubical.Algebra.CommSemiring.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.SIP using (TypeWithStr)

open import Cubical.Algebra.CommMonoid
open import Cubical.Algebra.Monoid

private
  variable
    ℓ ℓ' : Level

record IsCommSemiring {R : Type ℓ}
                  (0r 1r : R) (_+_ _·_ : R → R → R) : Type ℓ where

  field
    +IsCommMonoid  : IsCommMonoid 0r _+_
    ·IsCommMonoid  : IsCommMonoid 1r _·_
    ·LDist+        : (x y z : R) → x · (y + z) ≡ (x · y) + (x · z)
    AnnihilL       : (x : R) → 0r · x ≡ 0r

  open IsCommMonoid +IsCommMonoid public
    renaming
      ( isSemigroup to +IsSemigroup
      ; isMonoid    to +IsMonoid)

  open IsCommMonoid ·IsCommMonoid public
    renaming
      ( isSemigroup to ·IsSemigroup
      ; isMonoid    to ·IsMonoid)
    hiding
      ( is-set ) -- We only want to export one proof of this

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

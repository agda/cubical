{-# OPTIONS --safe #-}
module Cubical.Algebra.Semiring.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.SIP using (TypeWithStr)

open import Cubical.Algebra.CommMonoid
open import Cubical.Algebra.Monoid

private
  variable
    ℓ ℓ' : Level

record IsSemiring {R : Type ℓ}
                  (0r 1r : R) (_+_ _·_ : R → R → R) : Type ℓ where

  field
    +IsCommMonoid  : IsCommMonoid 0r _+_
    ·IsMonoid      : IsMonoid 1r _·_
    ·LDist+        : (x y z : R) → x · (y + z) ≡ (x · y) + (x · z)
    ·RDist+        : (x y z : R) → (x + y) · z ≡ (x · z) + (y · z)
    AnnihilL       : (x : R) → 0r · x ≡ 0r
    AnnihilR       : (x : R) → x · 0r ≡ 0r

  open IsCommMonoid +IsCommMonoid public
    renaming
      ( isSemigroup to +IsSemigroup
      ; isMonoid    to +IsMonoid)

  open IsMonoid ·IsMonoid public
    renaming
      ( isSemigroup to ·IsSemigroup )
    hiding
      ( is-set ) -- We only want to export one proof of this

record SemiringStr (A : Type ℓ) : Type (ℓ-suc ℓ) where

  field
    0r      : A
    1r      : A
    _+_     : A → A → A
    _·_     : A → A → A
    isSemiring  : IsSemiring 0r 1r _+_ _·_

  infixl 7 _·_
  infixl 6 _+_

  open IsSemiring isSemiring public

Semiring : ∀ ℓ → Type (ℓ-suc ℓ)
Semiring ℓ = TypeWithStr ℓ SemiringStr

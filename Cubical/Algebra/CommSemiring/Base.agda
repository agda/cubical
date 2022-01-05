{-# OPTIONS --safe #-}
module Cubical.Algebra.CommSemiring.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.SIP

open import Cubical.Algebra.CommMonoid
open import Cubical.Algebra.Monoid

private
  variable
    ℓ ℓ' : Level

record IsCommSemiring {R : Type ℓ}
                  (0r 1r : R) (_+_ _·_ : R → R → R) : Type ℓ where

  field
    +IsCommMonoid : IsCommMonoid 0r _+_
    ·IsMonoid  : IsMonoid 1r _·_
    ·RDist+        : (x y z : R) → x · (y + z) ≡ (x · y) + (x · z)
    ·LDist+        : (x y z : R) → (x + y) · z ≡ (x · z) + (y · z)
    0LAnnihil      : (x : R) → 0r · x ≡ 0r
    0RAnnihil      : (x : R) → x · 0r ≡ 0r

  open IsCommMonoid +IsCommMonoid public
    renaming
      ( assoc       to +Assoc
      ; identity    to +Identity
      ; lid         to +Lid
      ; rid         to +Rid
      ; comm        to +Comm
      ; isSemigroup to +IsSemigroup
      ; isMonoid    to +IsMonoid)

  open IsMonoid ·IsMonoid public
    renaming
      ( assoc       to ·Assoc
      ; identity    to ·Identity
      ; lid         to ·Lid
      ; rid         to ·Rid
      ; isSemigroup to ·IsSemigroup )
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

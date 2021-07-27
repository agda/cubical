
{-
Module in which commutative monoids are defined.
-}

{-# OPTIONS --safe #-}
module Cubical.Algebra.CommMonoid.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.SIP

open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid


private
  variable
    ℓ ℓ' : Level

record IsCommMonoid {M : Type ℓ}
                    (ε : M) (_·_ : M → M → M) : Type ℓ where

  constructor iscommmonoid

  field
    isMonoid : IsMonoid ε _·_
    comm     : (x y : M) → x · y ≡ y · x

  open IsMonoid isMonoid public

record CommMonoidStr (M : Type ℓ) : Type (ℓ-suc ℓ) where

  constructor commmonoidstr

  field
    ε            : M
    _·_          : M → M → M
    isCommMonoid : IsCommMonoid ε _·_

  infixr 7 _·_

  open IsCommMonoid isCommMonoid public

CommMonoid : ∀ ℓ → Type (ℓ-suc ℓ)
CommMonoid ℓ = TypeWithStr ℓ CommMonoidStr

makeIsCommMonoid : {M : Type ℓ} {ε : M} {_·_ : M → M → M}
                 (is-setM : isSet M)
                 (assoc   : (x y z : M) → x · (y · z) ≡ (x · y) · z)
                 (rid     : (x : M) → x · ε ≡ x)
                 (comm    : (x y : M) → x · y ≡ y · x)
               → IsCommMonoid ε _·_
makeIsCommMonoid is-setM assoc rid comm =
  iscommmonoid (makeIsMonoid is-setM assoc rid (λ x → comm _ _ ∙ rid x)) comm

makeCommMonoid : {M : Type ℓ} (ε : M) (_·_ : M → M → M)
               (is-setM : isSet M)
               (assoc : (x y z : M) → x · (y · z) ≡ (x · y) · z)
               (rid : (x : M) → x · ε ≡ x)
               (comm    : (x y : M) → x · y ≡ y · x)
             → CommMonoid ℓ
makeCommMonoid ε _·_ is-setM assoc rid comm =
  _ , commmonoidstr ε _·_ (makeIsCommMonoid is-setM assoc rid comm)

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
    ·DistR+        : (x y z : R) → x · (y + z) ≡ (x · y) + (x · z)
    ·DistL+        : (x y z : R) → (x + y) · z ≡ (x · z) + (y · z)
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

makeIsSemiring : {R : Type ℓ} {0r 1r : R} {_+_ _·_ : R → R → R}
                 (is-setR : isSet R)
                 (+Assoc : (x y z : R) → x + (y + z) ≡ (x + y) + z)
                 (+IdR : (x : R) → x + 0r ≡ x)
                 (+Comm : (x y : R) → x + y ≡ y + x)
                 (·Assoc : (x y z : R) → x · (y · z) ≡ (x · y) · z)
                 (·IdR : (x : R) → x · 1r ≡ x)
                 (·IdL : (x : R) → 1r · x ≡ x)
                 (·LDist+ : (x y z : R) → x · (y + z) ≡ (x · y) + (x · z))
                 (·RDist+ : (x y z : R) → (x + y) · z ≡ (x · z) + (y · z))
                 (AnnihilR : (x : R) → x · 0r ≡ 0r)
                 (AnnihilL : (x : R) → 0r · x ≡ 0r)
               → IsSemiring 0r 1r _+_ _·_
makeIsSemiring is-setR +Assoc +IdR +Comm ·Assoc ·IdR ·IdL ·DistR+ ·DistL+ AnnihilR AnnihilL
  = isSR
  where module IS = IsSemiring
        isSR : IsSemiring _ _ _ _
        IS.+IsCommMonoid isSR = makeIsCommMonoid is-setR +Assoc +IdR +Comm
        IS.·IsMonoid isSR = makeIsMonoid is-setR ·Assoc ·IdR ·IdL
        IS.·DistR+ isSR = ·DistR+
        IS.·DistL+ isSR = ·DistL+
        IS.AnnihilL isSR = AnnihilL
        IS.AnnihilR isSR = AnnihilR

Semiring→AbGroup : Semiring ℓ → CommMonoid ℓ
Semiring→AbGroup S .fst = fst S
Semiring→AbGroup S .snd = commMonoidStr
 where
   open CommMonoidStr
   +CM = IsSemiring.+IsCommMonoid (SemiringStr.isSemiring (snd S))

   commMonoidStr : CommMonoidStr (fst S)
   ε commMonoidStr = _
   _·_ commMonoidStr = _
   isCommMonoid commMonoidStr = +CM

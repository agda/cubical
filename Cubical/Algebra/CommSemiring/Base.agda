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

CommSemiring→Semiring : CommSemiring ℓ → Semiring ℓ
CommSemiring→Semiring CS .fst = CS .fst
CommSemiring→Semiring CS .snd = str
  where
    open IsCommSemiring
    open CommSemiringStr
    open SemiringStr

    CS-str = CS .snd

    str : SemiringStr (CS .fst)
    0r str = CS-str .0r
    1r str = CS-str .1r
    _+_ str = CS-str ._+_
    _·_ str = CS-str ._·_
    isSemiring str = (CS-str .isCommSemiring) .isSemiring

makeIsCommSemiring :
  {R : Type ℓ} {0r 1r : R} {_+_ _·_ : R → R → R}
  (is-setR : isSet R)
  (+Assoc : (x y z : R) → x + (y + z) ≡ (x + y) + z)
  (+IdR : (x : R) → x + 0r ≡ x)
  (+Comm : (x y : R) → x + y ≡ y + x)
  (·Assoc : (x y z : R) → x · (y · z) ≡ (x · y) · z)
  (·IdR : (x : R) → x · 1r ≡ x)
  (·DistR+ : (x y z : R) → x · (y + z) ≡ (x · y) + (x · z))
  (AnnihilL : (x : R) → 0r · x ≡ 0r)
  (·Comm : (x y : R) → x · y ≡ y · x)
  → IsCommSemiring 0r 1r _+_ _·_
makeIsCommSemiring {_+_ = _+_} {_·_ = _·_}
  is-setR +Assoc +IdR +Comm ·Assoc ·IdR ·DistR+ AnnihilL ·Comm = x
  where
    x : IsCommSemiring _ _ _ _
    IsCommSemiring.isSemiring x =
      makeIsSemiring
        is-setR +Assoc +IdR +Comm ·Assoc
        ·IdR (λ x → ·Comm _ x ∙ (·IdR x))
        ·DistR+ (λ x y z → (x + y) · z       ≡⟨ ·Comm (x + y) z ⟩
                           z · (x + y)       ≡⟨ ·DistR+ z x y ⟩
                           (z · x) + (z · y) ≡[ i ]⟨ (·Comm z x i + ·Comm z y i) ⟩
                           (x · z) + (y · z) ∎ )
        ( λ x → ·Comm x _ ∙ AnnihilL x) AnnihilL
    IsCommSemiring.·Comm x = ·Comm

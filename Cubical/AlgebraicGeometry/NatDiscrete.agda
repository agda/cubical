-- {-# OPTIONS --safe #-}
module Cubical.AlgebraicGeometry.NatDiscrete where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Nat

private
  variable
    @♭ ♭ℓ : Level

data ♭ (@♭ A : Type ♭ℓ) : Type ♭ℓ where
    _^♭ : (@♭ a : A) → ♭ A


counit : {@♭ ♭ℓ : Level} {@♭ A : Type ♭ℓ} → ♭ A → A
counit (a ^♭) = a

♭map : {@♭ ♭ℓ ♭ℓ′ : Level} {@♭ A : Type ♭ℓ} {@♭ B : Type ♭ℓ′}
       → (@♭ f : A → B) → ♭ A → ♭ B
♭map f (a ^♭) = (f a) ^♭

♭nat : {@♭ ♭ℓ ♭ℓ′ : Level} {@♭ A : Type ♭ℓ} {@♭ B : Type ♭ℓ′}
        → (@♭ f : A → B)
        → (@♭ x : A) → ♭map f (x ^♭) ≡ (f x) ^♭
♭nat f x = refl

isDiscreteℕ : isEquiv (counit {A = ℕ})
isDiscreteℕ = snd (isoToEquiv (iso counit inv linv rinv))
  where
    inv = λ { zero → zero ^♭ ; (suc x) → ♭map suc (inv x)}
    comm : (x : ℕ) → counit (inv (suc x)) ≡ suc (counit (inv x))
    comm x = {!!}
    linv = λ { zero → refl ; (suc x) → {!cong suc (linv x)!}}
    rinv = λ { (zero ^♭) → refl ; (suc a ^♭) → {!rinv (a ^♭)!}}

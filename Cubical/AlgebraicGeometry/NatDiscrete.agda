-- {-# OPTIONS --safe #-}
module Cubical.AlgebraicGeometry.NatDiscrete where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function

open import Cubical.Data.Nat
open import Cubical.Data.Unit

{-
  In Mike Shulman's real cohesive homotopty type theory,
  a judgement of the form `x :: A` is read as `x is a crisp
  variable of type A`. In Agda a declaration `@♭ x : A` can
  be used in a way similar. It is only possible to declare a
  variable like that, if all variables appearing in `A` were
  also introduced in this way. If this is the case, we say
  that `A` is crisp.
-}

private
  variable
    @♭ ♭ℓ : Level
    ℓ : Level

data ♭ (@♭ A : Type ♭ℓ) : Type ♭ℓ where
    _^♭ : (@♭ a : A) → ♭ A

counit : {@♭ ♭ℓ : Level} {@♭ A : Type ♭ℓ} → ♭ A → A
counit (a ^♭) = a

♭map : {@♭ ♭ℓ ♭ℓ′ : Level} {@♭ A : Type ♭ℓ} {@♭ B : Type ♭ℓ′}
       → (@♭ f : A → B) → ♭ A → ♭ B
♭map f (a ^♭) = (f a) ^♭

♭-induction : {@♭ ♭ℓ : Level} {@♭ A : Type ♭ℓ} (C : ♭ A → Type ℓ)
              → (f₀ : (@♭ u : A) → C (u ^♭))
              → (M : ♭ A)
              → (C M)
♭-induction C f₀ (a ^♭) = f₀ a

♭nat : {@♭ ♭ℓ ♭ℓ′ : Level} {@♭ A : Type ♭ℓ} {@♭ B : Type ♭ℓ′}
        → (@♭ f : A → B)
        → (x : ♭ A) → f (counit x) ≡ counit (♭map f x)
♭nat f (x ^♭) = refl

isDiscreteUnit : isEquiv (counit {A = Unit})
isDiscreteUnit = snd (isoToEquiv (iso counit inv linv rinv))
  where
    inv = λ {tt → tt ^♭}
    linv = λ {tt → refl}
    rinv = λ {(tt ^♭) → refl}

isDiscreteℕ : isEquiv (counit {A = ℕ})
isDiscreteℕ = snd (isoToEquiv (iso counit inv linv rinv))
  where
    inv = λ { zero → zero ^♭ ; (suc x) → ♭map suc (inv x)}
    linv = λ { zero → refl ;
              (suc x) →
                   counit (inv (suc x))    ≡⟨ sym (♭nat suc (inv x)) ⟩
                   suc (counit (inv x))    ≡⟨ cong suc (linv x) ⟩
                   suc x ∎}
    rinv = λ {
              (zero ^♭) → refl ;
              (suc a ^♭) → ♭map suc (inv a) ≡⟨ cong (♭map suc) (rinv (a ^♭)) ⟩ suc a ^♭ ∎
           }

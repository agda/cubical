-- {-# OPTIONS --safe #-}
module Cubical.Modalities.Flat where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function

open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Int

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
        → (x : ♭ A) → counit (♭map f x) ≡ f (counit x)
♭nat f (x ^♭) = refl

isCrisplyDiscrete : {@♭ ♭ℓ : Level}
                    → (@♭ A : Type ♭ℓ) → Type ♭ℓ
isCrisplyDiscrete A = isEquiv (counit {A = A})

isDiscreteUnit : isCrisplyDiscrete Unit
isDiscreteUnit = snd (isoToEquiv (iso counit inv linv rinv))
  where
    inv = λ {tt → tt ^♭}
    linv = λ {tt → refl}
    rinv = λ {(tt ^♭) → refl}
private
  counitInvℕ : ℕ → ♭ ℕ
  counitInvℕ zero = zero ^♭
  counitInvℕ (suc x) = ♭map suc (counitInvℕ x)

  linvℕ : (n : ℕ) → counit (counitInvℕ n) ≡ n
  linvℕ zero = refl
  linvℕ (suc x) =
         counit (counitInvℕ (suc x))    ≡⟨ ♭nat suc (counitInvℕ x) ⟩
         suc (counit (counitInvℕ x))    ≡⟨ cong suc (linvℕ x) ⟩
         suc x ∎

  rinvℕ : (n : ♭ ℕ) → counitInvℕ (counit n) ≡ n
  rinvℕ (zero ^♭) = refl
  rinvℕ (suc a ^♭) =
              ♭map suc (counitInvℕ a)  ≡⟨ cong (♭map suc) (rinvℕ (a ^♭)) ⟩
              suc a ^♭ ∎

isDiscreteℕ : isCrisplyDiscrete ℕ
isDiscreteℕ = snd (isoToEquiv (iso counit counitInvℕ linvℕ rinvℕ))

isDiscreteℤ : isCrisplyDiscrete ℤ
isDiscreteℤ = snd (isoToEquiv (iso counit inv linv rinv))
  where
    inv = λ { (pos n) → ♭map pos (counitInvℕ n) ;
              (negsuc n) → ♭map negsuc (counitInvℕ n)}
    linv = λ { (pos n) →
                 counit (inv (pos n))          ≡⟨ ♭nat pos (counitInvℕ n) ⟩
                 pos (counit (counitInvℕ n))   ≡⟨ cong pos (linvℕ n) ⟩
                 (pos n) ∎ ;
               (negsuc n) →
                 counit (inv (negsuc n))         ≡⟨ ♭nat negsuc (counitInvℕ n) ⟩
                 negsuc (counit (counitInvℕ n))  ≡⟨ cong negsuc (linvℕ n) ⟩
                 negsuc n ∎}
    rinv = λ { (pos n ^♭) → cong (♭map pos) (rinvℕ (n ^♭)) ;
               (negsuc n ^♭) → cong (♭map negsuc) (rinvℕ (n ^♭))}

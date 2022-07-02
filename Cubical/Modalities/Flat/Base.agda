{-# OPTIONS --safe #-}
module Cubical.Modalities.Flat.Base where

open import Cubical.Foundations.Prelude

{-
  In Mike Shulman's real cohesive homotopty type theory
  (see https://arxiv.org/pdf/1509.07584.pdf),
  a judgement of the form `x :: A` is read as `x is a crisp
  variable of type A`. In Agda a declaration `@♭ x : A` can
  be used in a way similar. It is only possible to declare a
  variable like that, if all variables appearing in `A` were
  also introduced in this way. If this is the case, we say
  that `A` is crisp.
-}

private variable
  {-
    Variable generalization mostly doesn't work for crisp contexts,
    so the crisp levels are not used too much.
  -}
  @♭ ♭ℓ : Level
  ℓ ℓ' : Level

data ♭ (@♭ A : Type ♭ℓ) : Type ♭ℓ where
    _^♭ : (@♭ a : A) → ♭ A

counit : {@♭ ♭ℓ : Level} {@♭ A : Type ♭ℓ} → ♭ A → A
counit (a ^♭) = a

♭map : {@♭ ♭ℓ ♭ℓ′ : Level} {@♭ A : Type ♭ℓ} {@♭ B : Type ♭ℓ′}
       → (@♭ f : A → B) → ♭ A → ♭ B
♭map f (a ^♭) = (f a) ^♭

♭-Induction : {@♭ ♭ℓ : Level} {@♭ A : Type ♭ℓ} (C : ♭ A → Type ℓ)
              → (f₀ : (@♭ u : A) → C (u ^♭))
              → (M : ♭ A)
              → (C M)
♭-Induction C f₀ (a ^♭) = f₀ a

{-
  Lemma 5.1 (Shulman's real cohesion)
-}
crisp♭-Induction : {@♭ ♭ℓ ♭ℓ' : Level} {@♭ A : Type ♭ℓ}
                   → (@♭ C : (@♭ x : ♭ A) → Type ♭ℓ')
                   → (@♭ N : (@♭ u : A) → C (u ^♭))
                   → (@♭ M : ♭ A) → C M
crisp♭-Induction C N (a ^♭) = N a

♭nat : {@♭ ♭ℓ ♭ℓ′ : Level} {@♭ A : Type ♭ℓ} {@♭ B : Type ♭ℓ′}
        → (@♭ f : A → B)
        → (x : ♭ A) → counit (♭map f x) ≡ f (counit x)
♭nat f (x ^♭) = refl

{-# OPTIONS --cubical #-}
module Cubical.Experiments.Epi where
  open import Cubical.Data.Unit
  open import Cubical.Foundations.Everything
  open import Cubical.Functions.Surjection
  open import Cubical.HITs.PropositionalTruncation

  postulate
    Ω-ext : ∀ {ℓ} {p q : hProp ℓ} → (p .fst → q .fst ) → (q .fst → p .fst) → p ≡ q

  ⊤* : ∀ {ℓ} → hProp ℓ
  ⊤* = Unit* , λ _ _ _ → tt*

  module _ {ℓ ℓ' : Level} {X : Type ℓ} {Y : Type ℓ'} where

    -- obs: for epi⇒surjective to go through we require a stronger
    -- hypothesis that one would expect:
    -- f must cancel functions from a higher universe.
    rightCancellable : (f : X → Y) → Type _
    rightCancellable f = ∀ {Z : Type (ℓ-suc (ℓ-max ℓ ℓ'))} → ∀ (g g' : Y → Z) → (∀ x → g (f x) ≡ g' (f x)) → ∀ y → g y ≡ g' y

    epi⇒surjective : (f : X → Y) → rightCancellable f → isSurjection f
    epi⇒surjective f rc y = transport (cong fst (fact₂ y)) tt*
        where hasPreimage : (X → Y) → Y → hProp _
              hasPreimage f y = ∥ fiber f y ∥ , propTruncIsProp

              fact₁ : ∀ x → ⊤* ≡ hasPreimage f (f x)
              fact₁ x = Ω-ext (λ _ → ∣ (x , refl) ∣) (λ _ → tt*)

              fact₂ : ∀ y → ⊤* ≡ hasPreimage f y
              fact₂ = rc _ _ fact₁

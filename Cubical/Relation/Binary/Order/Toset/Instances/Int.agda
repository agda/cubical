module Cubical.Relation.Binary.Order.Toset.Instances.Int where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sum
open import Cubical.HITs.PropositionalTruncation

open import Cubical.Data.Int
open import Cubical.Data.Int.Order renaming (_≤_ to _≤ℤ_)

open import Cubical.Relation.Binary.Order.Toset

open TosetStr

ℤ≤Toset : Toset ℓ-zero ℓ-zero
fst ℤ≤Toset = ℤ
_≤_ (snd ℤ≤Toset) = _≤ℤ_
isToset (snd ℤ≤Toset) = isTosetℤ≤
  where
    open IsToset
    abstract
      isTosetℤ≤ : IsToset _≤ℤ_
      isTosetℤ≤ .is-set         = isSetℤ
      isTosetℤ≤ .is-prop-valued = λ _ _ → isProp≤
      isTosetℤ≤ .is-refl        = λ _ → isRefl≤
      isTosetℤ≤ .is-trans       = λ _ _ _ → isTrans≤
      isTosetℤ≤ .is-antisym     = λ _ _ → isAntisym≤
      isTosetℤ≤ .is-total a b with a ≟ b
      ... | lt a<b = ∣ inl (<-weaken a<b) ∣₁
      ... | eq a≡b = ∣ inl (subst (a ≤ℤ_) a≡b isRefl≤) ∣₁
      ... | gt b<a = ∣ inr (<-weaken b<a) ∣₁

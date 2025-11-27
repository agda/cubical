module Cubical.Relation.Binary.Order.Toset.Instances.Int.Fast where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sum
open import Cubical.HITs.PropositionalTruncation

open import Cubical.Data.Int.Fast
open import Cubical.Data.Int.Fast.Order renaming (_≤_ to _≤ℤ_)

open import Cubical.Relation.Binary.Order.Toset

open import Cubical.Relation.Binary
open BinaryRelation

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
      isTosetℤ≤ .is-prop-valued = λ a b → isProp≤ {a} {b}
      isTosetℤ≤ .is-refl        = λ _ → isRefl≤
      isTosetℤ≤ .is-trans       = λ a b c → isTrans≤ {a} {b} {c}
      isTosetℤ≤ .is-antisym     = λ _ _ → isAntisym≤
      isTosetℤ≤ .is-total a b with a ≟ b
      ... | lt a<b = ∣ inl (<-weaken {a} {b} a<b) ∣₁
      ... | eq a≡b = ∣ inl (subst (a ≤ℤ_) a≡b isRefl≤) ∣₁
      ... | gt b<a = ∣ inr (<-weaken {b} {a} b<a) ∣₁

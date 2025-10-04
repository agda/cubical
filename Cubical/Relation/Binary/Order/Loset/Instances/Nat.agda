module Cubical.Relation.Binary.Order.Loset.Instances.Nat where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sum
open import Cubical.HITs.PropositionalTruncation

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order renaming (_<_ to _<ℕ_)

open import Cubical.Relation.Binary.Order.Loset

open LosetStr

ℕ<Loset : Loset ℓ-zero ℓ-zero
fst ℕ<Loset = ℕ
_<_ (snd ℕ<Loset) = _<ℕ_
isLoset (snd ℕ<Loset) = isLosetℕ<
  where
    open IsLoset
    abstract
      isLosetℕ< : IsLoset _<ℕ_
      isLosetℕ< .is-set         = isSetℕ
      isLosetℕ< .is-prop-valued = λ _ _ → isProp≤
      isLosetℕ< .is-irrefl      = λ _ → ¬m<m
      isLosetℕ< .is-trans       = λ _ _ _ → <-trans
      isLosetℕ< .is-asym        = λ a b a<b b<a → ¬m<m (<-trans a<b b<a)
      isLosetℕ< .is-weakly-linear a b c a<b with a ≟ c
      ... | lt a<c = ∣ inl a<c ∣₁
      ... | eq a≡c = ∣ inr (subst (_<ℕ b) a≡c a<b) ∣₁
      ... | gt c<a = ∣ inr (<-trans c<a a<b) ∣₁
      isLosetℕ< .is-connected a b (¬a<b , ¬b<a) = ≤-antisym (<-asym' ¬b<a) (<-asym' ¬a<b)

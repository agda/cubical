module Cubical.Relation.Binary.Order.StrictOrder.Instances.Nat where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Sum
open import Cubical.HITs.PropositionalTruncation

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order renaming (_<_ to _<ℕ_)

open import Cubical.Relation.Binary.Order.StrictOrder.Base

open StrictOrderStr

ℕ<StrictOrder : StrictOrder ℓ-zero ℓ-zero
fst ℕ<StrictOrder = ℕ
_<_ (snd ℕ<StrictOrder) = _<ℕ_
isStrictOrder (snd ℕ<StrictOrder) = isStrictOrderℕ<
  where
    open IsStrictOrder
    abstract
      isStrictOrderℕ< : IsStrictOrder _<ℕ_
      isStrictOrderℕ< .is-set           = isSetℕ
      isStrictOrderℕ< .is-prop-valued   = λ _ _ → isProp≤
      isStrictOrderℕ< .is-irrefl        = λ _ → ¬m<m
      isStrictOrderℕ< .is-trans         = λ _ _ _ → <-trans
      isStrictOrderℕ< .is-asym          = λ a b a<b b<a → ¬m<m (<-trans a<b b<a)
      isStrictOrderℕ< .is-weakly-linear a b c a<b with a ≟ c
      ... | lt a<c = ∣ inl a<c ∣₁
      ... | eq a≡c = ∣ inr (subst (_<ℕ b) a≡c a<b) ∣₁
      ... | gt c<a = ∣ inr (<-trans c<a a<b) ∣₁

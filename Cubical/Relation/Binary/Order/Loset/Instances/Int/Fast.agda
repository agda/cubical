module Cubical.Relation.Binary.Order.Loset.Instances.Int.Fast where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sum
open import Cubical.HITs.PropositionalTruncation

open import Cubical.Data.Empty as ⊥

open import Cubical.Data.Int.Fast
open import Cubical.Data.Int.Fast.Order renaming (_<_ to _<ℤ_)

open import Cubical.Relation.Binary.Order.Loset

open import Cubical.Relation.Binary
open BinaryRelation

open LosetStr

ℤ<Loset : Loset ℓ-zero ℓ-zero
fst ℤ<Loset = ℤ
_<_ (snd ℤ<Loset) = _<ℤ_
isLoset (snd ℤ<Loset) = isLosetℤ<
  where
    open IsLoset
    abstract
      isLosetℤ< : IsLoset _<ℤ_
      isLosetℤ< .is-set         = isSetℤ
      isLosetℤ< .is-prop-valued = λ a b → isProp< {a} {b}
      isLosetℤ< .is-irrefl      = λ _ → isIrrefl<
      isLosetℤ< .is-trans       = λ a b c → isTrans< {a} {b} {c}
      isLosetℤ< .is-asym        = λ a b a<b b<a → isIrrefl< (isTrans< {a} {b} {a} a<b b<a)
      isLosetℤ< .is-weakly-linear a b c a<b with a ≟ c
      ... | lt a<c = ∣ inl a<c ∣₁
      ... | eq a≡c = ∣ inr (subst (_<ℤ b) a≡c a<b) ∣₁
      ... | gt c<a = ∣ inr (isTrans< {c} {a} {b} c<a a<b) ∣₁
      isLosetℤ< .is-connected a b (¬a<b , ¬b<a) with a ≟ b
      ... | lt a<b = ⊥.rec (¬a<b a<b)
      ... | eq a≡b = a≡b
      ... | gt b<a = ⊥.rec (¬b<a b<a)

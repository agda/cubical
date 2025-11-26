module Cubical.Relation.Binary.Order.Loset.Instances.Rationals.Fast where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sum
open import Cubical.HITs.PropositionalTruncation

open import Cubical.Data.Empty as ⊥

open import Cubical.Data.Rationals.Fast
open import Cubical.Data.Rationals.Fast.Order renaming (_<_ to _<ℚ_)

open import Cubical.Relation.Binary.Order.Loset

open LosetStr

ℚ<Loset : Loset ℓ-zero ℓ-zero
fst ℚ<Loset = ℚ
_<_ (snd ℚ<Loset) = _<ℚ_
isLoset (snd ℚ<Loset) = isLosetℚ<
  where
    open IsLoset
    abstract
      isLosetℚ< : IsLoset _<ℚ_
      isLosetℚ< .is-set           = isSetℚ
      isLosetℚ< .is-prop-valued   = isProp<
      isLosetℚ< .is-irrefl        = isIrrefl<
      isLosetℚ< .is-trans         = isTrans<
      isLosetℚ< .is-asym          = isAsym<
      isLosetℚ< .is-weakly-linear = isWeaklyLinear<
      isLosetℚ< .is-connected     = isConnected<

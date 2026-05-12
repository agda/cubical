module Cubical.Algebra.Monoid.Instances.List where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.List

open import Cubical.Algebra.Monoid


ListMonoid : (Σ Type isSet) → Monoid ℓ-zero
fst (ListMonoid (A , _)) = (List A)
MonoidStr.ε (snd (ListMonoid _)) = []
MonoidStr._·_ (snd (ListMonoid _)) = _++_
MonoidStr.isMonoid (snd (ListMonoid (_ , pf))) = makeIsMonoid (isOfHLevelList 0 pf)
                                    (λ x y z → sym (++-assoc x y z)) ++-unit-r (λ _ → refl)

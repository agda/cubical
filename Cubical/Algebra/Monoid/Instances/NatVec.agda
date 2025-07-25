module Cubical.Algebra.Monoid.Instances.NatVec where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ ; isSetℕ)
open import Cubical.Data.Vec
open import Cubical.Data.Vec.OperationsNat

open import Cubical.Algebra.Monoid


NatVecMonoid : (n : ℕ) → Monoid ℓ-zero
fst (NatVecMonoid n) = Vec ℕ n
MonoidStr.ε (snd (NatVecMonoid n)) = replicate 0
MonoidStr._·_ (snd (NatVecMonoid n)) = _+n-vec_
MonoidStr.isMonoid (snd (NatVecMonoid n)) = makeIsMonoid (VecPath.isOfHLevelVec 0 n isSetℕ)
                                                       +n-vec-assoc +n-vec-rid +n-vec-lid

{-

The naive, but incorrect, way to define the integers as a HIT.

This file mainly contains a proof that IsoInt ≢ Int, and ends with a
 demonstration of how the same proof strategy fails for BiInvℤ.

-}
module Cubical.Experiments.IsoInt.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Int
open import Cubical.Data.Nat
open import Cubical.Data.Empty

open import Cubical.Relation.Nullary


data IsoInt : Type₀ where
  zero : IsoInt
  suc : IsoInt -> IsoInt

  -- suc is an isomorphism:
  pred : IsoInt -> IsoInt
  suc-pred : ∀ z -> suc (pred z) ≡ z
  pred-suc : ∀ z -> pred (suc z) ≡ z


suc-iso : Iso IsoInt IsoInt
suc-iso = record { fun = suc ; inv = pred ; rightInv = suc-pred ; leftInv = pred-suc }


-- this submodule is adapted from Section 5 of
--  http://www.cs.ru.nl/~herman/PUBS/HIT-programming.pdf

module NonTrivial where

  -- these two paths are distinct!
  p₁ p₂ : Path IsoInt (suc (pred (suc zero))) (suc zero)
  p₁ i = suc-pred (suc zero) i
  p₂ i = suc (pred-suc zero i)

  -- to prove this we map into S¹, sending p₁ to refl and p₂ to loop

  open import Cubical.HITs.S1

  toS¹ : IsoInt → S¹
  toS¹ zero           = base
  toS¹ (suc x)        = toS¹ x
  toS¹ (pred x)       = toS¹ x
  toS¹ (suc-pred x i) = refl {x = toS¹ x} i
  toS¹ (pred-suc x i) = rotLoop (toS¹ x) i

  p₁≡refl : cong toS¹ p₁ ≡ refl
  p₁≡refl = refl

  p₂≡loop : cong toS¹ p₂ ≡ loop
  p₂≡loop = refl

  -- this is enough to show that p₁ and p₂ cannot be equal
  p₁≢p₂ : ¬ (p₁ ≡ p₂)
  p₁≢p₂ eq = znots 0≡1
    where -- using winding numbers, p₁ ≡ p₂ implies 0 ≡ 1
          0≡1 : 0 ≡ 1
          0≡1 = injPos (cong (winding ∘ cong toS¹) eq)


¬isSet-IsoInt : ¬ (isSet IsoInt)
¬isSet-IsoInt pf = NonTrivial.p₁≢p₂ (pf _ _ NonTrivial.p₁ NonTrivial.p₂)

¬Int≡IsoInt : ¬ (ℤ ≡ IsoInt)
¬Int≡IsoInt p = ¬isSet-IsoInt (subst isSet p isSetℤ)



private

  -- Note: this same proof strategy fails for BiInvℤ!

  open import Cubical.Data.Int.MoreInts.BiInvInt hiding (zero; suc; pred; suc-pred; pred-suc)
  import Cubical.Data.Int.MoreInts.BiInvInt as BiI

  p₁ p₂ : Path BiInvℤ (BiI.suc (BiI.pred (BiI.suc BiI.zero))) (BiI.suc BiI.zero)
  p₁ i = BiI.suc-pred (BiI.suc BiI.zero) i
  p₂ i = BiI.suc (BiI.pred-suc BiI.zero i)

  open import Cubical.HITs.S1

  toS¹ : BiInvℤ → S¹
  toS¹ BiI.zero            = base
  toS¹ (BiI.suc x)         = toS¹ x
  toS¹ (BiI.predr x)       = toS¹ x
  toS¹ (BiI.predl x)       = toS¹ x
  toS¹ (BiI.suc-predr x i) = refl {x = toS¹ x} i
  toS¹ (BiI.predl-suc x i) = rotLoop (toS¹ x) i

  -- still p₂ maps to loop...
  p₂≡loop : cong toS¹ p₂ ≡ loop
  p₂≡loop = refl

  open import Cubical.Foundations.GroupoidLaws

  -- ...but now so does p₁!
  p₁≡loop : cong toS¹ p₁ ≡ loop
  p₁≡loop = sym (decodeEncode base (cong toS¹ p₁)) ∙ sym (lUnit loop)

  -- if we use BiI.predr instead of BiI.pred (≡ BiI.predl) in p₁ and p₂,
  --  both paths in S¹ are refl

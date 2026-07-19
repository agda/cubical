
module Cubical.Foundations.Interpolate where

open import Cubical.Foundations.Prelude

-- An "interpolation" operator on the De Morgan interval. Interpolates
-- along t from i to j (see first two properties below.)
interpolateI : I → I → I → I
interpolateI t i j = (~ t ∧ i) ∨ (t ∧ j) ∨ (i ∧ j)

-- I believe this is the simplest De Morgan function on three
-- variables which satisfies all (or even most) of the nice properties
-- below.

module _
  {A : Type} {p : I → A} {i j k l m : I}
  where
  _ : p (interpolateI i0 i j) ≡ p i
  _ = refl

  _ : p (interpolateI i1 i j) ≡ p j
  _ = refl

  _ : p (interpolateI (~ i) j k) ≡ p (interpolateI i k j)
  _ = refl

  _ : p (interpolateI i i0 i1) ≡ p i
  _ = refl

  _ : p (interpolateI i i1 i0) ≡ p (~ i)
  _ = refl

  _ : p (interpolateI i j j) ≡ p j
  _ = refl

  _ : p (interpolateI i (interpolateI j k l) m) ≡ p (interpolateI j (interpolateI i k m) (interpolateI i l m))
  _ = refl

  _ : p (interpolateI i j (interpolateI k l m)) ≡ p (interpolateI k (interpolateI i j l) (interpolateI i j m))
  _ = refl

  _ : p (interpolateI i i0 j) ≡ p (i ∧ j)
  _ = refl

  _ : p (interpolateI i i1 j) ≡ p (~ i ∨ j)
  _ = refl

  _ : p (interpolateI i j i0) ≡ p (~ i ∧ j)
  _ = refl

  _ : p (interpolateI i j i1) ≡ p (i ∨ j)
  _ = refl

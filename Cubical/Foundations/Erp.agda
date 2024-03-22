{-# OPTIONS --safe #-}

module Cubical.Foundations.Erp where

open import Cubical.Foundations.Prelude

-- "erp": a De Morgan interpolation. Interpolates along t from i to j
-- (see first two properties below.)
erp : I → I → I → I
erp t i j = (~ t ∧ i) ∨ (t ∧ j) ∨ (i ∧ j)

-- I believe this is the simplest De Morgan function on three
-- variables which satisfies all (or even most) of the nice properties
-- below.

-- I used to call this "lerp" but it is not really a linear
-- interpolation. I considered "derp" but it seemed a bit too silly...

module _
  {A : Type} {p : I → A} {i j k l m : I}
  where
  _ : p (erp i0 i j) ≡ p i
  _ = refl

  _ : p (erp i1 i j) ≡ p j
  _ = refl

  _ : p (erp (~ i) j k) ≡ p (erp i k j)
  _ = refl

  _ : p (erp i i0 i1) ≡ p i
  _ = refl

  _ : p (erp i i1 i0) ≡ p (~ i)
  _ = refl

  _ : p (erp i j j) ≡ p j
  _ = refl

  _ : p (erp i (erp j k l) m) ≡ p (erp j (erp i k m) (erp i l m))
  _ = refl

  _ : p (erp i j (erp k l m)) ≡ p (erp k (erp i j l) (erp i j m))
  _ = refl

  _ : p (erp i i0 j) ≡ p (i ∧ j)
  _ = refl

  _ : p (erp i i1 j) ≡ p (~ i ∨ j)
  _ = refl

  _ : p (erp i j i0) ≡ p (~ i ∧ j)
  _ = refl

  _ : p (erp i j i1) ≡ p (i ∨ j)
  _ = refl

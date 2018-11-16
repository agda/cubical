{-# OPTIONS --cubical #-}
module Cubical.HITs.Join where

open import Cubical.Core.Primitives
open import Cubical.Core.Prelude
open import Cubical.Core.Glue

open import Cubical.HITs.S1
open import Cubical.HITs.S3

data join {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') : Set (ℓ-max ℓ ℓ') where
  inl : A → join A B
  inr : B → join A B
  push : ∀ a b → inl a ≡ inr b

S³→joinS¹S¹ : S³ → join S¹ S¹
S³→joinS¹S¹ base = inl base
S³→joinS¹S¹ (surf i j k) =
  let facek01 : I → I → I → join S¹ S¹
      facek01 i j k = hfill (λ l → λ { (j = i0) → push base base (~ l ∧ ~ k)
                                     ; (j = i1) → push base base (~ l ∧ ~ k)
                                     ; (k = i0) → push (loop j) base (~ l)
                                     ; (k = i1) → inl base })
                            (inc (push base base (~ k))) i
  in hcomp (λ l → λ { (i = i0) → facek01 i1 j l
                    ; (i = i1) → push base (loop k) (~ l)
                    ; (j = i0) → push base (loop k) (i ∧ ~ l)
                    ; (j = i1) → push base (loop k) (i ∧ ~ l)
                   ; (k = i0) → facek01 (~ i) j l
                   ; (k = i1) → facek01 (~ i) j l })
           (push (loop j) (loop k) i)

joinS¹S¹→S³ : join S¹ S¹ → S³
joinS¹S¹→S³ (inl x) = base
joinS¹S¹→S³ (inr x) = base
joinS¹S¹→S³ (push base b i) = base
joinS¹S¹→S³ (push (loop x) base i) = base
joinS¹S¹→S³ (push (loop i) (loop j) k) = surf i j k

{-# OPTIONS --cubical #-}
module Cubical.HITs.Join where

open import Cubical.Core.Primitives
open import Cubical.Core.Prelude
open import Cubical.Core.Glue

open import Cubical.Basics.Equiv
open import Cubical.HITs.S1
open import Cubical.HITs.S3

data join {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') : Set (ℓ-max ℓ ℓ') where
  inl : A → join A B
  inr : B → join A B
  push : ∀ a b → inl a ≡ inr b

facek01 : I → I → I → join S¹ S¹
facek01 i j k = hfill (λ l → λ { (j = i0) → push base base (~ l ∧ ~ k)
                               ; (j = i1) → push base base (~ l ∧ ~ k)
                               ; (k = i0) → push (loop j) base (~ l)
                               ; (k = i1) → inl base })
                      (inc (push base base (~ k))) i

border-contraction : I → I → I → I → join S¹ S¹
border-contraction i j k m =
  hfill (λ l → λ { (i = i0) → facek01 i1 j l
                 ; (i = i1) → push base (loop k) (~ l)
                 ; (j = i0) → push base (loop k) (i ∧ ~ l)
                 ; (j = i1) → push base (loop k) (i ∧ ~ l)
                 ; (k = i0) → facek01 (~ i) j l
                 ; (k = i1) → facek01 (~ i) j l })
        (inc (push (loop j) (loop k) i)) m

S³→joinS¹S¹ : S³ → join S¹ S¹
S³→joinS¹S¹ base = inl base
S³→joinS¹S¹ (surf j k i) = border-contraction i j k i1

joinS¹S¹→S³ : join S¹ S¹ → S³
joinS¹S¹→S³ (inl x) = base
joinS¹S¹→S³ (inr x) = base
joinS¹S¹→S³ (push base b i) = base
joinS¹S¹→S³ (push (loop x) base i) = base
joinS¹S¹→S³ (push (loop i) (loop j) k) = surf i j k

connection : I → I → I → I → S³
connection i j k l =
  hfill (λ m → λ { (k = i0) → joinS¹S¹→S³ (facek01 m i j)
                 ; (k = i1) → base
                 ; (j = i0) → base
                 ; (j = i1) → base
                 ; (i = i0) → base
                 ; (i = i1) → base })
        (inc base) l

S³→joinS¹S¹→S³ : ∀ x → joinS¹S¹→S³ (S³→joinS¹S¹ x) ≡ x
S³→joinS¹S¹→S³ base l = base
S³→joinS¹S¹→S³ (surf j k i) l =
  hcomp (λ m → λ { (l = i0) → joinS¹S¹→S³ (border-contraction i j k m)
                 ; (l = i1) → surf j k i
                 ; (i = i0) → connection j m l i1
                 ; (i = i1) → base
                 ; (j = i0) → base
                 ; (j = i1) → base
                 ; (k = i0) → connection j m l (~ i)
                 ; (k = i1) → connection j m l (~ i) })
                 (surf j k i)

joinS¹S¹→S³→joinS¹S¹ : ∀ x → S³→joinS¹S¹ (joinS¹S¹→S³ x) ≡ x
joinS¹S¹→S³→joinS¹S¹ (inl base) l = inl base
joinS¹S¹→S³→joinS¹S¹ (inl (loop i)) l = facek01 i1 i (~ l)
joinS¹S¹→S³→joinS¹S¹ (inr base) l = push base base l
joinS¹S¹→S³→joinS¹S¹ (inr (loop i)) l = push base (loop i) l
joinS¹S¹→S³→joinS¹S¹ (push base base i) l = push base base (i ∧ l)
joinS¹S¹→S³→joinS¹S¹ (push base (loop k) i) l = push base (loop k) (i ∧ l)
joinS¹S¹→S³→joinS¹S¹ (push (loop k) base i) l = facek01 (~ i) k (~ l)
joinS¹S¹→S³→joinS¹S¹ (push (loop j) (loop k) i) l = border-contraction i j k (~ l)

S³≡joinS¹S¹ : S³ ≡ join S¹ S¹
S³≡joinS¹S¹ = isoToPath S³→joinS¹S¹ joinS¹S¹→S³ joinS¹S¹→S³→joinS¹S¹ S³→joinS¹S¹→S³

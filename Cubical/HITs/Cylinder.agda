{-# OPTIONS --cubical #-}

module Cubical.HITs.Cylinder where

open import Cubical.Core.Everything

import Cubical.Basics.Everything as Basics
open Basics hiding (inl; inr)

module _ {ℓ} (A : Set ℓ) where
  data Cylinder : Set ℓ where
    inl : A → Cylinder
    inr : A → Cylinder
    cross : ∀ x → inl x ≡ inr x

  include : A ⊎ A → Cylinder
  include (Basics.inl x) = inl x
  include (Basics.inr x) = inr x

  module _ {ℓ'} {B : Cylinder → Set ℓ'}
                (f : (x : A) → B (inl x))
                (g : (x : A) → B (inr x))
                (p : ∀ x → PathP (λ i → B (cross x i)) (f x) (g x))
    where
    elimCyl : (c : Cylinder) → B c
    elimCyl (inl x) = f x
    elimCyl (inr x) = g x
    elimCyl (cross x i) = p x i

  private
    out : Cylinder → A
    out (inl x) = x
    out (inr x) = x
    out (cross x i) = x

    inl-out : ∀ c → inl (out c) ≡ c
    inl-out (inl x) = refl
    inl-out (inr x) = cross x
    inl-out (cross x i) = λ j → cross x (i ∧ j)

    out-inl : ∀ x → out (inl x) ≡ x
    out-inl x = refl

  cylEquiv : Cylinder ≃ A
  cylEquiv = isoToEquiv out inl out-inl inl-out

module Interval where
  open import Cubical.HITs.Interval

  cyl : Interval → Cylinder Unit
  cyl zero = inl _
  cyl one = inr _
  cyl (seg i) = cross _ i

  int : Cylinder Unit → Interval
  int (inl _) = zero
  int (inr _) = one
  int (cross _ i) = seg i

  int-cyl : ∀ i → int (cyl i) ≡ i
  int-cyl zero = refl
  int-cyl one = refl
  int-cyl (seg i) = refl

  cyl-int : ∀ c → cyl (int c) ≡ c
  cyl-int (inl _) = refl
  cyl-int (inr _) = refl
  cyl-int (cross _ i) = refl

  cylIntEquiv : Cylinder Unit ≃ Interval
  cylIntEquiv = isoToEquiv int cyl int-cyl cyl-int

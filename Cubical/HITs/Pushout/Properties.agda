{-

This file contains:

- 3×3 lemma for pushouts
  Written by: Loïc Pujet, April 2019

-}

{-# OPTIONS --cubical --safe #-}

module Cubical.HITs.Pushout.Properties where

open import Cubical.Core.Glue

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Data.Prod.Base
open import Cubical.Data.Unit

open import Cubical.HITs.Pushout.Base

{-

  3×3 lemma for pushouts

Let Aᵢⱼ denote a type, fᵢⱼ a map and Hᵢⱼ a homotopy. Given a diagram of the following shape:

A00 ←—f01—— A02 ——f03—→ A04
 ↑           ↑           ↑
f10   H11   f12   H13   f14
 |           |           |
A20 ←—f21—— A22 ——f23—→ A24
 |           |           |
f30   H31   f32   H33   f34
 ↓           ↓           ↓
A40 ←—f41—— A42 ——f43—→ A44

one can build its colimit from pushouts in two ways:
- either build pushouts A□0, A□2, A□4 of the lines and then build the pushout A□○ of the resulting
  diagram A□0 ←—f□1—— A□2 ——f□3—→ A□4 ;
- or build pushouts of the columns and build the pushout A○□ of the resulting diagram A0□ ← A2□ → A4□.

Then the lemma states there is an equivalence A□○ ≃ A○□.

-}

module 3x3-span
  (A00 A02 A04 A20 A22 A24 A40 A42 A44 : Type₀)

  (f10 : A20 → A00)
  (f12 : A22 → A02)
  (f14 : A24 → A04)

  (f30 : A20 → A40)
  (f32 : A22 → A42)
  (f34 : A24 → A44)

  (f01 : A02 → A00)
  (f21 : A22 → A20)
  (f41 : A42 → A40)

  (f03 : A02 → A04)
  (f23 : A22 → A24)
  (f43 : A42 → A44)

  (H11 : ∀ x → f01 (f12 x) ≡ f10 (f21 x))
  (H13 : ∀ x → f03 (f12 x) ≡ f14 (f23 x))
  (H31 : ∀ x → f41 (f32 x) ≡ f30 (f21 x))
  (H33 : ∀ x → f43 (f32 x) ≡ f34 (f23 x))
  where

  -- pushouts of the lines
  A□0 : Type₀
  A□0 = Pushout f10 f30

  A□2 : Type₀
  A□2 = Pushout f12 f32

  A□4 : Type₀
  A□4 = Pushout f14 f34

  -- maps between pushouts
  f□1 : A□2 → A□0
  f□1 (inl x) = inl (f01 x)
  f□1 (inr x) = inr (f41 x)
  f□1 (push a j) = ((λ i → inl (H11 a i))
                   ∙∙ push (f21 a)
                   ∙∙ (λ i → inr (H31 a (~ i)))) j

  f□3 : A□2 → A□4
  f□3 (inl x) = inl (f03 x)
  f□3 (inr x) = inr (f43 x)
  f□3 (push a j) = ((λ i → inl (H13 a i))
                   ∙∙ push (f23 a)
                   ∙∙ (λ i → inr (H33 a (~ i)))) j

  -- total pushout
  A□○ : Type₀
  A□○ = Pushout f□1 f□3

  -- pushouts of the columns
  A0□ : Type₀
  A0□ = Pushout f01 f03

  A2□ : Type₀
  A2□ = Pushout f21 f23

  A4□ : Type₀
  A4□ = Pushout f41 f43

  -- maps between pushouts
  f1□ : A2□ → A0□
  f1□ (inl x) = inl (f10 x)
  f1□ (inr x) = inr (f14 x)
  f1□ (push a j) = ((λ i → inl (H11 a (~ i)))
                   ∙∙ push (f12 a)
                   ∙∙ (λ i → inr (H13 a i))) j

  f3□ : A2□ → A4□
  f3□ (inl x) = inl (f30 x)
  f3□ (inr x) = inr (f34 x)
  f3□ (push a j) = ((λ i → inl (H31 a (~ i)))
                   ∙∙ push (f32 a)
                   ∙∙ (λ i → inr (H33 a i))) j

  -- total pushout
  A○□ : Type₀
  A○□ = Pushout f1□ f3□

  -- forward map of the equivalence A□○ ≃ A○□
  forward-l : A□0 → A○□
  forward-l (inl x) = inl (inl x)
  forward-l (inr x) = inr (inl x)
  forward-l (push a i) = push (inl a) i

  forward-r : A□4 → A○□
  forward-r (inl x) = inl (inr x)
  forward-r (inr x) = inr (inr x)
  forward-r (push a i) = push (inr a) i

  forward-filler : A22 → I → I → I → A○□
  forward-filler a i j = hfill (λ t → λ { (i = i0) → inl (doubleCompPath-filler (λ k → inl (H11 a (~ k))) (push (f12 a)) (λ k → inr (H13 a k)) j (~ t))
                                 ; (i = i1) → inr (doubleCompPath-filler (λ k → inl (H31 a (~ k))) (push (f32 a)) (λ k → inr (H33 a k)) j (~ t))
                                 ; (j = i0) → forward-l (doubleCompPath-filler (λ k → inl (H11 a k)) (push (f21 a)) (λ k → inr (H31 a (~ k))) i t)
                                 ; (j = i1) → forward-r (doubleCompPath-filler (λ k → inl (H13 a k)) (push (f23 a)) (λ k → inr (H33 a (~ k))) i t) })
                        (inS (push (push a j) i))

  A□○→A○□ : A□○ → A○□
  A□○→A○□ (inl x) = forward-l x
  A□○→A○□ (inr x) = forward-r x
  A□○→A○□ (push (inl x) i) = inl (push x i)
  A□○→A○□ (push (inr x) i) = inr (push x i)
  A□○→A○□ (push (push a i) j) = forward-filler a i j i1

  -- backward map
  backward-l : A0□ → A□○
  backward-l (inl x) = inl (inl x)
  backward-l (inr x) = inr (inl x)
  backward-l (push a i) = push (inl a) i

  backward-r : A4□ → A□○
  backward-r (inl x) = inl (inr x)
  backward-r (inr x) = inr (inr x)
  backward-r (push a i) = push (inr a) i

  backward-filler : A22 → I → I → I → A□○
  backward-filler a i j = hfill (λ t → λ { (i = i0) → inl (doubleCompPath-filler (λ k → inl (H11 a k)) (push (f21 a)) (λ k → inr (H31 a (~ k))) j (~ t))
                                 ; (i = i1) → inr (doubleCompPath-filler (λ k → inl (H13 a k)) (push (f23 a)) (λ k → inr (H33 a (~ k))) j (~ t))
                                 ; (j = i0) → backward-l (doubleCompPath-filler (λ k → inl (H11 a (~ k))) (push (f12 a)) (λ k → inr (H13 a k)) i t)
                                 ; (j = i1) → backward-r (doubleCompPath-filler (λ k → inl (H31 a (~ k))) (push (f32 a)) (λ k → inr (H33 a k)) i t) })
                        (inS (push (push a j) i))

  A○□→A□○ : A○□ → A□○
  A○□→A□○ (inl x) = backward-l x
  A○□→A□○ (inr x) = backward-r x
  A○□→A□○ (push (inl x) i) = inl (push x i)
  A○□→A□○ (push (inr x) i) = inr (push x i)
  A○□→A□○ (push (push a i) j) = backward-filler a i j i1

  -- first homotopy
  homotopy1-l : ∀ x → A□○→A○□ (backward-l x) ≡ inl x
  homotopy1-l (inl x) = refl
  homotopy1-l (inr x) = refl
  homotopy1-l (push a i) = refl

  homotopy1-r : ∀ x → A□○→A○□ (backward-r x) ≡ inr x
  homotopy1-r (inl x) = refl
  homotopy1-r (inr x) = refl
  homotopy1-r (push a i) = refl

  A○□→A□○→A○□ : ∀ x → A□○→A○□ (A○□→A□○ x) ≡ x
  A○□→A□○→A○□ (inl x) = homotopy1-l x
  A○□→A□○→A○□ (inr x) = homotopy1-r x
  A○□→A□○→A○□ (push (inl x) i) k = push (inl x) i
  A○□→A□○→A○□ (push (inr x) i) k = push (inr x) i
  A○□→A□○→A○□ (push (push a i) j) k =
    hcomp (λ t → λ { (i = i0) → forward-l (doubleCompPath-filler (λ k → inl (H11 a k)) (push (f21 a)) (λ k → inr (H31 a (~ k))) j (~ t))
                   ; (i = i1) → forward-r (doubleCompPath-filler (λ k → inl (H13 a k)) (push (f23 a)) (λ k → inr (H33 a (~ k))) j (~ t))
                   ; (j = i0) → homotopy1-l (doubleCompPath-filler (λ k → inl (H11 a (~ k))) (push (f12 a)) (λ k → inr (H13 a k)) i t) k
                   ; (j = i1) → homotopy1-r (doubleCompPath-filler (λ k → inl (H31 a (~ k))) (push (f32 a)) (λ k → inr (H33 a k)) i t) k
                   ; (k = i0) → A□○→A○□ (backward-filler a i j t)
                   ; (k = i1) → forward-filler a j i (~ t) })
          (forward-filler a j i i1)

  -- second homotopy
  homotopy2-l : ∀ x → A○□→A□○ (forward-l x) ≡ inl x
  homotopy2-l (inl x) = refl
  homotopy2-l (inr x) = refl
  homotopy2-l (push a i) = refl

  homotopy2-r : ∀ x → A○□→A□○ (forward-r x) ≡ inr x
  homotopy2-r (inl x) = refl
  homotopy2-r (inr x) = refl
  homotopy2-r (push a i) = refl

  A□○→A○□→A□○ : ∀ x → A○□→A□○ (A□○→A○□ x) ≡ x
  A□○→A○□→A□○ (inl x) = homotopy2-l x
  A□○→A○□→A□○ (inr x) = homotopy2-r x
  A□○→A○□→A□○ (push (inl x) i) k = push (inl x) i
  A□○→A○□→A□○ (push (inr x) i) k = push (inr x) i
  A□○→A○□→A□○ (push (push a i) j) k =
    hcomp (λ t → λ { (i = i0) → backward-l (doubleCompPath-filler (λ k → inl (H11 a (~ k))) (push (f12 a)) (λ k → inr (H13 a k)) j (~ t))
                   ; (i = i1) → backward-r (doubleCompPath-filler (λ k → inl (H31 a (~ k))) (push (f32 a)) (λ k → inr (H33 a k)) j (~ t))
                   ; (j = i0) → homotopy2-l (doubleCompPath-filler (λ k → inl (H11 a k)) (push (f21 a)) (λ k → inr (H31 a (~ k))) i t) k
                   ; (j = i1) → homotopy2-r (doubleCompPath-filler (λ k → inl (H13 a k)) (push (f23 a)) (λ k → inr (H33 a (~ k))) i t) k
                   ; (k = i0) → A○□→A□○ (forward-filler a i j t)
                   ; (k = i1) → backward-filler a j i (~ t) })
          (backward-filler a j i i1)

  -- equivalence
  Pushout3x3 : A□○ ≡ A○□
  Pushout3x3 = isoToPath (iso A□○→A○□ A○□→A□○ A○□→A□○→A○□ A□○→A○□→A□○)

Pushout3x3 : ∀ A00 A02 A04 A20 A22 A24 A40 A42 A44 f10 f12 f14 f30 f32 f34 f01 f21 f41 f03 f23 f43 H11 H13 H31 H33 →
  3x3-span.A□○ A00 A02 A04 A20 A22 A24 A40 A42 A44 f10 f12 f14 f30 f32 f34 f01 f21 f41 f03 f23 f43 H11 H13 H31 H33
  ≡ 3x3-span.A○□ A00 A02 A04 A20 A22 A24 A40 A42 A44 f10 f12 f14 f30 f32 f34 f01 f21 f41 f03 f23 f43 H11 H13 H31 H33
Pushout3x3 = 3x3-span.Pushout3x3

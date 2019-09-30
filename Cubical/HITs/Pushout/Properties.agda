{-

This file contains:

- Homotopy natural equivalences of pushout spans
  Written by: Loïc Pujet, September 2019

- 3×3 lemma for pushouts
  Written by: Loïc Pujet, April 2019

-}

{-# OPTIONS --cubical --safe #-}

module Cubical.HITs.Pushout.Properties where

open import Cubical.Core.Glue

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HAEquiv
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Data.Prod.Base
open import Cubical.Data.Unit

open import Cubical.HITs.Pushout.Base

{-
  Definition of pushout diagrams
-}

record 3-span : Type₁ where
  field
    A0 A2 A4 : Type₀
    f1 : A2 → A0
    f3 : A2 → A4

spanPushout : (s : 3-span) → Type₀
spanPushout s = Pushout (3-span.f1 s) (3-span.f3 s)

{-
  Definition of a homotopy natural diagram equivalence
-}

record 3-span-equiv (s1 : 3-span) (s2 : 3-span) : Type₀ where
   field
     e0 : 3-span.A0 s1 ≃ 3-span.A0 s2
     e2 : 3-span.A2 s1 ≃ 3-span.A2 s2
     e4 : 3-span.A4 s1 ≃ 3-span.A4 s2
     H1 : ∀ x → 3-span.f1 s2 (e2 .fst x) ≡ e0 .fst (3-span.f1 s1 x)
     H3 : ∀ x → 3-span.f3 s2 (e2 .fst x) ≡ e4 .fst (3-span.f3 s1 x)

{-
  Proof that the pushouts of equivalent diagrams are equal
-}

spanEquivToPath : {s1 : 3-span} → {s2 : 3-span} → (e : 3-span-equiv s1 s2)
                  → spanPushout s1 ≡ spanPushout s2
spanEquivToPath {s1} {s2} e = p1≡p2
  where
    open 3-span-equiv e
    open isHAEquiv
    open 3-span

    -- we use half-adjoint equivalences because we will need the higher coherences
    -- built inside the equivalences
    hae0 : isHAEquiv (fst e0)
    hae0 = snd (equiv→HAEquiv e0)

    hae2 : isHAEquiv (fst e2)
    hae2 = snd (equiv→HAEquiv e2)

    hae4 : isHAEquiv (fst e4)
    hae4 = snd (equiv→HAEquiv e4)

    -- construct a pushout map from a homotopy coherent equivalence
    filler1 : A2 s1 → I → I → spanPushout s2
    filler1 a = doubleCompPath-filler (λ j → inl (H1 a (~ j)))
                                      (push (e2 .fst a))
                                      (λ j → inr (H3 a j))

    p1→p2 : spanPushout s1 → spanPushout s2
    p1→p2 (inl x) = inl (e0 .fst x)
    p1→p2 (inr x) = inr (e4 .fst x)
    p1→p2 (push a i) = filler1 a i i1

    -- construct a homotopy coherent inverse
    filler2 : A2 s2 → I → I → spanPushout s1
    filler2 a = doubleCompPath-filler (λ j → inl (sec hae0 (f1 s1 (g hae2 a)) j))
                                      (push (g hae2 a))
                                      (λ j → inr (sec hae4 (f3 s1 (g hae2 a)) (~ j)))

    filler3 : A2 s2 → I → I → spanPushout s1
    filler3 a = doubleCompPath-filler (λ j → inl (g hae0 (H1 (g hae2 a) j)))
                                      (λ i → filler2 a i i1)
                                      (λ j → inr (g hae4 (H3 (g hae2 a) (~ j))))

    filler4 : A2 s2 → I → I → spanPushout s1
    filler4 a = doubleCompPath-filler ((λ j → inl (g hae0 (f1 s2 (ret hae2 a (~ j))))))
                                      (λ i → filler3 a i i1)
                                      (λ j → inr (g hae4 (f3 s2 (ret hae2 a j))))

    p2→p1 : spanPushout s2 → spanPushout s1
    p2→p1 (inl x) = inl (g hae0 x)
    p2→p1 (inr x) = inr (g hae4 x)
    p2→p1 (push a i) = filler4 a i i1

    -- construct a homotopy coherent retraction
    sq1 : (x : A2 s2) → I → I → spanPushout s2
    sq1 x i j = hcomp (λ k → λ { (i = i0) → inl (ret hae0 ((f1 s2 (e2 .fst (g hae2 x)))) j)
                               ; (i = i1) → inl (com hae0 (f1 s1 (g hae2 x)) (~ k) j)
                               ; (j = i0) → inl (e0 .fst (g hae0 (H1 (g hae2 x) i)))
                               ; (j = i1) → inl (H1 (g hae2 x) i) })
                      (inl (ret hae0 (H1 (g hae2 x) i) j))

    sq2 : (x : A2 s2) → I → I → spanPushout s2
    sq2 x i j = hcomp (λ k → λ { (i = i0) → inr (ret hae4 ((f3 s2 (e2 .fst (g hae2 x)))) j)
                               ; (i = i1) → inr (com hae4 (f3 s1 (g hae2 x)) (~ k) j)
                               ; (j = i0) → inr (e4 .fst (g hae4 (H3 (g hae2 x) i)))
                               ; (j = i1) → inr (H3 (g hae2 x) i) })
                      (inr (ret hae4 (H3 (g hae2 x) i) j))

    sq3 : (x : A2 s2) → I → I → spanPushout s2
    sq3 x i j = hcomp (λ k → λ { (i = i0) → sq1 x (~ k) j
                               ; (i = i1) → sq2 x (~ k) j
                               ; (j = i0) → p1→p2 (filler3 x i k)
                               ; (j = i1) → filler1 (g hae2 x) i (~ k) })
                      (p1→p2 (filler2 x i (~ j)))

    sq4 : (x : A2 s2) → I → I → spanPushout s2
    sq4 x i j = hcomp (λ k → λ { (i = i0) → inl (ret hae0 (f1 s2 (ret hae2 x k)) j)
                               ; (i = i1) → inr (ret hae4 (f3 s2 (ret hae2 x k)) j)
                               ; (j = i0) → p1→p2 (filler4 x i k)
                               ; (j = i1) → push (ret hae2 x k) i })
                      (sq3 x i j)

    p2→p1→p2 : ∀ x → p1→p2 (p2→p1 x) ≡ x
    p2→p1→p2 (inl x) i = inl (ret hae0 x i)
    p2→p1→p2 (inr x) i = inr (ret hae4 x i)
    p2→p1→p2 (push a j) i = sq4 a j i

    -- construct a homotopy coherent section
    sq5 : (x : A2 s1) → I → I → spanPushout s1
    sq5 x i j = hcomp (λ k → λ { (i = i0) → inl (g hae0 (f1 s2 (com hae2 x k j)))
                               ; (i = i1) → inl (g hae0 (e0 .fst (f1 s1 (sec hae2 x j))))
                               ; (j = i0) → inl (g hae0 (H1 (g hae2 (e2 .fst x)) i))
                               ; (j = i1) → inl (g hae0 (H1 x i)) })
                      (inl (g hae0 (H1 (sec hae2 x j) i)))

    sq6 : (x : A2 s1) → I → I → spanPushout s1
    sq6 x i j = hcomp (λ k → λ { (i = i0) → inr (g hae4 (f3 s2 (com hae2 x k j)))
                               ; (i = i1) → inr (g hae4 (e4 .fst (f3 s1 (sec hae2 x j))))
                               ; (j = i0) → inr (g hae4 (H3 (g hae2 (e2 .fst x)) i))
                               ; (j = i1) → inr (g hae4 (H3 x i)) })
                      (inr (g hae4 (H3 (sec hae2 x j) i)))

    sq7 : (x : A2 s1) → I → I → spanPushout s1
    sq7 x i j = hcomp (λ k → λ { (i = i0) → sq5 x k (~ j)
                               ; (i = i1) → sq6 x k (~ j)
                               ; (j = i0) → p2→p1 (filler1 x i k)
                               ; (j = i1) → filler3 (e2 .fst x) i (~ k) })
                      (filler4 (e2 .fst x) i (~ j))

    sq8 : (x : A2 s1) → I → I → spanPushout s1
    sq8 x i j = hcomp (λ k → λ { (i = i0) → inl (sec hae0 (f1 s1 (sec hae2 x k)) j)
                               ; (i = i1) → inr (sec hae4 (f3 s1 (sec hae2 x k)) j)
                               ; (j = i0) → sq7 x i (~ k)
                               ; (j = i1) → push (sec hae2 x k) i })
                      (filler2 (e2 .fst x) i (~ j))

    p1→p2→p1 : ∀ x → p2→p1 (p1→p2 x) ≡ x
    p1→p2→p1 (inl x) i = inl (sec hae0 x i)
    p1→p2→p1 (inr x) i = inr (sec hae4 x i)
    p1→p2→p1 (push a j) i = sq8 a j i

    -- deduce equality of the pushouts
    p1≡p2 : spanPushout s1 ≡ spanPushout s2
    p1≡p2 = isoToPath (iso p1→p2 p2→p1 p2→p1→p2 p1→p2→p1)

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

record 3x3-span : Type₁ where
  field
    A00 A02 A04 A20 A22 A24 A40 A42 A44 : Type₀

    f10 : A20 → A00
    f12 : A22 → A02
    f14 : A24 → A04

    f30 : A20 → A40
    f32 : A22 → A42
    f34 : A24 → A44

    f01 : A02 → A00
    f21 : A22 → A20
    f41 : A42 → A40

    f03 : A02 → A04
    f23 : A22 → A24
    f43 : A42 → A44

    H11 : ∀ x → f01 (f12 x) ≡ f10 (f21 x)
    H13 : ∀ x → f03 (f12 x) ≡ f14 (f23 x)
    H31 : ∀ x → f41 (f32 x) ≡ f30 (f21 x)
    H33 : ∀ x → f43 (f32 x) ≡ f34 (f23 x)

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

  -- the claimed result
  3x3-lemma : A□○ ≡ A○□
  3x3-lemma = isoToPath (iso A□○→A○□ A○□→A□○ A○□→A□○→A○□ A□○→A○□→A□○)
    where
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

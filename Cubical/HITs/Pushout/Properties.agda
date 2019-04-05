{-# OPTIONS --cubical --safe #-}

module Cubical.HITs.Pushout.Properties where

open import Cubical.Core.Primitives
open import Cubical.Core.Prelude
open import Cubical.Core.Glue

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Data.Prod.Base
open import Cubical.Data.Unit

open import Cubical.HITs.Pushout.Base

-- 3×3 lemma for pushouts

{-
 
A00 ←—f01—— A02 ——f03—→ A04
 ↑           ↑           ↑
f10   H11   f12   H13   f14
 |           |           |
A20 ←—f21—— A22 ——f23—→ A24
 |           |           |
f30   H31   f32   H33   f34
 ↓           ↓           ↓
A40 ←—f41—— A42 ——f43—→ A44

-}

module 3x3 (A00 A02 A04 A20 A22 A24 A40 A42 A44 : Set)
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

  A□0 : Set
  A□0 = Pushout f10 f30

  A□2 : Set
  A□2 = Pushout f12 f32

  A□4 : Set
  A□4 = Pushout f14 f34

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
  
  A□○ : Set
  A□○ = Pushout f□1 f□3

  A0□ : Set
  A0□ = Pushout f01 f03

  A2□ : Set
  A2□ = Pushout f21 f23

  A4□ : Set
  A4□ = Pushout f41 f43

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

  A○□ : Set
  A○□ = Pushout f1□ f3□

  aux1 : A□0 → A○□
  aux1 (inl x) = inl (inl x)
  aux1 (inr x) = inr (inl x)
  aux1 (push a i) = push (inl a) i

  aux2 : A□4 → A○□
  aux2 (inl x) = inl (inr x)
  aux2 (inr x) = inr (inr x)
  aux2 (push a i) = push (inr a) i

  filler1 : A22 → I → I → I → A○□
  filler1 a i j = hfill (λ t → λ { (i = i0) → inl (doubleCompPath-filler (λ k → inl (H11 a (~ k))) (push (f12 a)) (λ k → inr (H13 a k)) j (~ t))
                                 ; (i = i1) → inr (doubleCompPath-filler (λ k → inl (H31 a (~ k))) (push (f32 a)) (λ k → inr (H33 a k)) j (~ t))
                                 ; (j = i0) → aux1 (doubleCompPath-filler (λ k → inl (H11 a k)) (push (f21 a)) (λ k → inr (H31 a (~ k))) i t)
                                 ; (j = i1) → aux2 (doubleCompPath-filler (λ k → inl (H13 a k)) (push (f23 a)) (λ k → inr (H33 a (~ k))) i t) })
                        (inS (push (push a j) i))

  A□○→A○□ : A□○ → A○□
  A□○→A○□ (inl x) = aux1 x
  A□○→A○□ (inr x) = aux2 x
  A□○→A○□ (push (inl x) i) = inl (push x i)
  A□○→A○□ (push (inr x) i) = inr (push x i)
  A□○→A○□ (push (push a i) j) = filler1 a i j i1

  aux3 : A0□ → A□○
  aux3 (inl x) = inl (inl x)
  aux3 (inr x) = inr (inl x)
  aux3 (push a i) = push (inl a) i

  aux4 : A4□ → A□○
  aux4 (inl x) = inl (inr x)
  aux4 (inr x) = inr (inr x)
  aux4 (push a i) = push (inr a) i

  filler2 : A22 → I → I → I → A□○
  filler2 a i j = hfill (λ t → λ { (i = i0) → inl (doubleCompPath-filler (λ k → inl (H11 a k)) (push (f21 a)) (λ k → inr (H31 a (~ k))) j (~ t))
                                 ; (i = i1) → inr (doubleCompPath-filler (λ k → inl (H13 a k)) (push (f23 a)) (λ k → inr (H33 a (~ k))) j (~ t))
                                 ; (j = i0) → aux3 (doubleCompPath-filler (λ k → inl (H11 a (~ k))) (push (f12 a)) (λ k → inr (H13 a k)) i t)
                                 ; (j = i1) → aux4 (doubleCompPath-filler (λ k → inl (H31 a (~ k))) (push (f32 a)) (λ k → inr (H33 a k)) i t) })
                        (inS (push (push a j) i))

  A○□→A□○ : A○□ → A□○
  A○□→A□○ (inl x) = aux3 x
  A○□→A□○ (inr x) = aux4 x
  A○□→A□○ (push (inl x) i) = inl (push x i)
  A○□→A□○ (push (inr x) i) = inr (push x i)
  A○□→A□○ (push (push a i) j) = filler2 a i j i1

  aux5 : ∀ x → A□○→A○□ (aux3 x) ≡ inl x
  aux5 (inl x) = refl
  aux5 (inr x) = refl
  aux5 (push a i) = refl

  aux6 : ∀ x → A□○→A○□ (aux4 x) ≡ inr x
  aux6 (inl x) = refl
  aux6 (inr x) = refl
  aux6 (push a i) = refl

  A○□→A□○→A○□ : ∀ x → A□○→A○□ (A○□→A□○ x) ≡ x
  A○□→A□○→A○□ (inl x) = aux5 x
  A○□→A□○→A○□ (inr x) = aux6 x
  A○□→A□○→A○□ (push (inl x) i) k = push (inl x) i
  A○□→A□○→A○□ (push (inr x) i) k = push (inr x) i
  A○□→A□○→A○□ (push (push a i) j) k =
    hcomp (λ t → λ { (i = i0) → aux1 (doubleCompPath-filler (λ k → inl (H11 a k)) (push (f21 a)) (λ k → inr (H31 a (~ k))) j (~ t))
                   ; (i = i1) → aux2 (doubleCompPath-filler (λ k → inl (H13 a k)) (push (f23 a)) (λ k → inr (H33 a (~ k))) j (~ t))
                   ; (j = i0) → aux5 (doubleCompPath-filler (λ k → inl (H11 a (~ k))) (push (f12 a)) (λ k → inr (H13 a k)) i t) k
                   ; (j = i1) → aux6 (doubleCompPath-filler (λ k → inl (H31 a (~ k))) (push (f32 a)) (λ k → inr (H33 a k)) i t) k
                   ; (k = i0) → A□○→A○□ (filler2 a i j t)
                   ; (k = i1) → filler1 a j i (~ t) })
          (filler1 a j i i1)

  aux7 : ∀ x → A○□→A□○ (aux1 x) ≡ inl x
  aux7 (inl x) = refl
  aux7 (inr x) = refl
  aux7 (push a i) = refl

  aux8 : ∀ x → A○□→A□○ (aux2 x) ≡ inr x
  aux8 (inl x) = refl
  aux8 (inr x) = refl
  aux8 (push a i) = refl

  A□○→A○□→A□○ : ∀ x → A○□→A□○ (A□○→A○□ x) ≡ x
  A□○→A○□→A□○ (inl x) = aux7 x
  A□○→A○□→A□○ (inr x) = aux8 x
  A□○→A○□→A□○ (push (inl x) i) k = push (inl x) i
  A□○→A○□→A□○ (push (inr x) i) k = push (inr x) i
  A□○→A○□→A□○ (push (push a i) j) k =
    hcomp (λ t → λ { (i = i0) → aux3 (doubleCompPath-filler (λ k → inl (H11 a (~ k))) (push (f12 a)) (λ k → inr (H13 a k)) j (~ t))
                   ; (i = i1) → aux4 (doubleCompPath-filler (λ k → inl (H31 a (~ k))) (push (f32 a)) (λ k → inr (H33 a k)) j (~ t))
                   ; (j = i0) → aux7 (doubleCompPath-filler (λ k → inl (H11 a k)) (push (f21 a)) (λ k → inr (H31 a (~ k))) i t) k
                   ; (j = i1) → aux8 (doubleCompPath-filler (λ k → inl (H13 a k)) (push (f23 a)) (λ k → inr (H33 a (~ k))) i t) k
                   ; (k = i0) → A○□→A□○ (filler1 a i j t)
                   ; (k = i1) → filler2 a j i (~ t) })
          (filler2 a j i i1)

  

  3x3 : A□○ ≡ A○□
  3x3 = isoToPath (iso A□○→A○□ A○□→A□○ A○□→A□○→A○□ A□○→A○□→A□○)


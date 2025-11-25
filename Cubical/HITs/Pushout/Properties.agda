{-

This file contains:
- Elimination principle for pushouts

- Homotopy natural equivalences of pushout spans
  Written by: Loïc Pujet, September 2019

- 3×3 lemma for pushouts
  Written by: Loïc Pujet, April 2019

- Homotopy natural equivalences of pushout spans
  (unpacked and avoiding transports)
-}


module Cubical.HITs.Pushout.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Path
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv.HalfAdjoint

open import Cubical.Relation.Nullary

open import Cubical.Relation.Nullary

open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.List
open import Cubical.Data.Sum

open import Cubical.HITs.Pushout.Base
open import Cubical.HITs.Pushout.Flattening
open import Cubical.HITs.Susp.Base

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    A : Type ℓ
    B : Type ℓ'
    C : Type ℓ''

{-
  Elimination for propositions
-}
elimProp : {f : A → B} {g : A → C}
  → (P : Pushout f g → Type ℓ''')
  → ((x : Pushout f g) → isProp (P x))
  → ((b : B) → P (inl b))
  → ((c : C) → P (inr c))
  → (x : Pushout f g) → P x
elimProp P isPropP PB PC (inl x) = PB x
elimProp P isPropP PB PC (inr x) = PC x
elimProp {f = f} {g = g} P isPropP PB PC (push a i) =
  isOfHLevel→isOfHLevelDep 1 isPropP (PB (f a)) (PC (g a)) (push a) i


{-
  Switching the span does not change the pushout
-}
pushoutSwitchEquiv : {f : A → B} {g : A → C}
  → Pushout f g ≃ Pushout g f
pushoutSwitchEquiv = isoToEquiv (iso f inv leftInv rightInv)
  where f = λ {(inr x) → inl x; (inl x) → inr x; (push a i) → push a (~ i)}
        inv = λ {(inr x) → inl x; (inl x) → inr x; (push a i) → push a (~ i)}
        leftInv = λ {(inl x) → refl; (inr x) → refl; (push a i) → refl}
        rightInv = λ {(inl x) → refl; (inr x) → refl; (push a i) → refl}


{-
  Direct proof that pushout along the identity gives an equivalence.
-}
pushoutIdfunEquiv : ∀ {ℓ ℓ'} {X : Type ℓ} {Y : Type ℓ'} (f : X → Y)
  → Y ≃ Pushout f (idfun X)
pushoutIdfunEquiv f = isoToEquiv (iso inl inv leftInv λ _ → refl)
  where
    inv : Pushout f (idfun _) → _
    inv (inl y) = y
    inv (inr x) = f x
    inv (push x i) = f x

    leftInv : section inl inv
    leftInv (inl y) = refl
    leftInv (inr x) = push x
    leftInv (push a i) j = push a (i ∧ j)

pushoutIdfunEquiv' : ∀ {ℓ ℓ'} {X : Type ℓ} {Y : Type ℓ'} (f : X → Y)
  → Y ≃ Pushout (idfun X) f
pushoutIdfunEquiv' f = compEquiv (pushoutIdfunEquiv _) pushoutSwitchEquiv

{-
  Definition of pushout diagrams
-}
module _ {ℓ₀ ℓ₂ ℓ₄ : Level} where
  private
    ℓ* = ℓ-maxList (ℓ₀ ∷ ℓ₂ ∷ ℓ₄ ∷ [])
  record  3-span : Type (ℓ-suc ℓ*) where
    field
      A0 : Type ℓ₀
      A2 : Type ℓ₂
      A4 : Type ℓ₄
      f1 : A2 → A0
      f3 : A2 → A4

  3span : {A0 : Type ℓ₀} {A2 : Type ℓ₂} {A4 : Type ℓ₄}
    → (A2 → A0) → (A2 → A4) → 3-span
  3span f1 f3 = record { f1 = f1 ; f3 = f3 }

  spanPushout : (s : 3-span) → Type ℓ*
  spanPushout s = Pushout (3-span.f1 s) (3-span.f3 s)

{-
  Definition of a homotopy natural diagram equivalence
-}

module _ {ℓ₀₀ ℓ₀₂ ℓ₀₄ : Level} {ℓ₂₀ ℓ₂₂ ℓ₂₄ : Level}  where
  private
    ℓ* = ℓ-maxList (ℓ₀₀ ∷ ℓ₀₂ ∷ ℓ₀₄ ∷ ℓ₂₀ ∷ ℓ₂₂ ∷ ℓ₂₄ ∷ [])
  record 3-span-equiv (s1 : 3-span {ℓ₀₀} {ℓ₀₂} {ℓ₀₄})
                      (s2 : 3-span {ℓ₂₀} {ℓ₂₂} {ℓ₂₄})
                    : Type (ℓ-suc ℓ*) where
     field
       e0 : 3-span.A0 s1 ≃ 3-span.A0 s2
       e2 : 3-span.A2 s1 ≃ 3-span.A2 s2
       e4 : 3-span.A4 s1 ≃ 3-span.A4 s2
       H1 : ∀ x → 3-span.f1 s2 (e2 .fst x) ≡ e0 .fst (3-span.f1 s1 x)
       H3 : ∀ x → 3-span.f3 s2 (e2 .fst x) ≡ e4 .fst (3-span.f3 s1 x)

  {-
    Proof that homotopy equivalent spans are in fact equal
  -}
module _ {ℓ₀ ℓ₂ ℓ₄ : Level} where
  spanEquivToPath : {s1 s2 : 3-span {ℓ₀} {ℓ₂} {ℓ₄}}
    → (e : 3-span-equiv s1 s2) → s1 ≡ s2
  spanEquivToPath {s1} {s2} e = spanPath
    where
      open 3-span-equiv e
      open 3-span

      path0 : A0 s1 ≡ A0 s2
      path0 = ua e0

      path2 : A2 s1 ≡ A2 s2
      path2 = ua e2

      path4 : A4 s1 ≡ A4 s2
      path4 = ua e4

      spanPath1 : I → 3-span
      spanPath1 i = record { A0 = path0 i ; A2 = path2 i ; A4 = path4 i ;
                             f1 = λ x → (transp (λ j → path0 (i ∧ j)) (~ i) (f1 s1 (transp (λ j → path2 (~ j ∧ i)) (~ i) x))) ;
                             f3 = λ x → (transp (λ j → path4 (i ∧ j)) (~ i) (f3 s1 (transp (λ j → path2 (~ j ∧ i)) (~ i) x))) }

      spanPath2 : I → 3-span
      spanPath2 i = record { A0 = A0 s2 ; A2 = A2 s2 ; A4 = A4 s2 ; f1 = f1Path i ; f3 = f3Path i }
        where
          f1Path : I → A2 s2 → A0 s2
          f1Path i x = ((uaβ e0 (f1 s1 (transport (λ j → path2 (~ j)) x)))
                       ∙ (H1 (transport (λ j → path2 (~ j)) x)) ⁻¹
                       ∙ (λ j → f1 s2 (uaβ e2 (transport (λ j → path2 (~ j)) x) (~ j)))
                       ∙ (λ j → f1 s2 (transportTransport⁻ path2 x j))) i

          f3Path : I → A2 s2 → A4 s2
          f3Path i x = ((uaβ e4 (f3 s1 (transport (λ j → path2 (~ j)) x)))
                       ∙ (H3 (transport (λ j → path2 (~ j)) x)) ⁻¹
                       ∙ (λ j → f3 s2 (uaβ e2 (transport (λ j → path2 (~ j)) x) (~ j)))
                       ∙ (λ j → f3 s2 (transportTransport⁻ path2 x j))) i

      spanPath : s1 ≡ s2
      spanPath = (λ i → spanPath1 i) ∙ (λ i → spanPath2 i)

  -- as a corollary, they have the same pushout
  spanEquivToPushoutPath : {s1 : 3-span} → {s2 : 3-span} → (e : 3-span-equiv s1 s2)
                           → spanPushout s1 ≡ spanPushout s2
  spanEquivToPushoutPath {s1} {s2} e = cong spanPushout (spanEquivToPath e)

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

record 3x3-span {ℓ₀₀ ℓ₀₂ ℓ₀₄ ℓ₂₀ ℓ₂₂ ℓ₂₄ ℓ₄₀ ℓ₄₂ ℓ₄₄ : Level} :
  Type (ℓ-suc (ℓ-maxList (ℓ₀₀ ∷ ℓ₀₂ ∷ ℓ₀₄ ∷ ℓ₂₀ ∷ ℓ₂₂ ∷ ℓ₂₄ ∷ ℓ₄₀ ∷ ℓ₄₂ ∷ ℓ₄₄ ∷ []))) where
  field
    A00 : Type ℓ₀₀
    A02 : Type ℓ₀₂
    A04 : Type ℓ₀₄
    A20 : Type ℓ₂₀
    A22 : Type ℓ₂₂
    A24 : Type ℓ₂₄
    A40 : Type ℓ₄₀
    A42 : Type ℓ₄₂
    A44 : Type ℓ₄₄

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
  A□0 : Type _
  A□0 = Pushout f10 f30

  A□2 : Type _
  A□2 = Pushout f12 f32

  A□4 : Type _
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
  A□○ : Type _
  A□○ = Pushout f□1 f□3

  -- pushouts of the columns
  A0□ : Type _
  A0□ = Pushout f01 f03

  A2□ : Type _
  A2□ = Pushout f21 f23

  A4□ : Type _
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
  A○□ : Type _
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
  forward-filler a i j = hfill (λ t → λ { (i = i0) → inl (doubleCompPath-filler (λ k → inl (H11 a (~ k))) (push (f12 a)) (λ k → inr (H13 a k)) (~ t) j)
                                 ; (i = i1) → inr (doubleCompPath-filler (λ k → inl (H31 a (~ k))) (push (f32 a)) (λ k → inr (H33 a k)) (~ t) j)
                                 ; (j = i0) → forward-l (doubleCompPath-filler (λ k → inl (H11 a k)) (push (f21 a)) (λ k → inr (H31 a (~ k))) t i)
                                 ; (j = i1) → forward-r (doubleCompPath-filler (λ k → inl (H13 a k)) (push (f23 a)) (λ k → inr (H33 a (~ k))) t i) })
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
  backward-filler a i j = hfill (λ t → λ { (i = i0) → inl (doubleCompPath-filler (λ k → inl (H11 a k)) (push (f21 a)) (λ k → inr (H31 a (~ k))) (~ t) j)
                                 ; (i = i1) → inr (doubleCompPath-filler (λ k → inl (H13 a k)) (push (f23 a)) (λ k → inr (H33 a (~ k))) (~ t) j)
                                 ; (j = i0) → backward-l (doubleCompPath-filler (λ k → inl (H11 a (~ k))) (push (f12 a)) (λ k → inr (H13 a k)) t i)
                                 ; (j = i1) → backward-r (doubleCompPath-filler (λ k → inl (H31 a (~ k))) (push (f32 a)) (λ k → inr (H33 a k)) t i) })
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
    hcomp (λ t → λ { (i = i0) → forward-l (doubleCompPath-filler (λ k → inl (H11 a k)) (push (f21 a)) (λ k → inr (H31 a (~ k))) (~ t) j)
                   ; (i = i1) → forward-r (doubleCompPath-filler (λ k → inl (H13 a k)) (push (f23 a)) (λ k → inr (H33 a (~ k))) (~ t) j)
                   ; (j = i0) → homotopy1-l (doubleCompPath-filler (λ k → inl (H11 a (~ k))) (push (f12 a)) (λ k → inr (H13 a k)) t i) k
                   ; (j = i1) → homotopy1-r (doubleCompPath-filler (λ k → inl (H31 a (~ k))) (push (f32 a)) (λ k → inr (H33 a k)) t i) k
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
    hcomp (λ t → λ { (i = i0) → backward-l (doubleCompPath-filler (λ k → inl (H11 a (~ k))) (push (f12 a)) (λ k → inr (H13 a k)) (~ t) j)
                   ; (i = i1) → backward-r (doubleCompPath-filler (λ k → inl (H31 a (~ k))) (push (f32 a)) (λ k → inr (H33 a k)) (~ t) j)
                   ; (j = i0) → homotopy2-l (doubleCompPath-filler (λ k → inl (H11 a k)) (push (f21 a)) (λ k → inr (H31 a (~ k))) t i) k
                   ; (j = i1) → homotopy2-r (doubleCompPath-filler (λ k → inl (H13 a k)) (push (f23 a)) (λ k → inr (H33 a (~ k))) t i) k
                   ; (k = i0) → A○□→A□○ (forward-filler a i j t)
                   ; (k = i1) → backward-filler a j i (~ t) })
          (backward-filler a j i i1)

  3x3-Iso : Iso A□○ A○□
  Iso.fun 3x3-Iso = A□○→A○□
  Iso.inv 3x3-Iso = A○□→A□○
  Iso.rightInv 3x3-Iso = A○□→A□○→A○□
  Iso.leftInv 3x3-Iso = A□○→A○□→A□○

  -- the claimed result
  3x3-lemma : A□○ ≡ A○□
  3x3-lemma = isoToPath 3x3-Iso

-- explicit characterisation of equivalences
-- Pushout f₁ g₁ ≃ Pushout f₂ g₂ avoiding
-- transports

open Iso
private
  module PushoutIso {ℓ : Level} {A₁ B₁ C₁ A₂ B₂ C₂ : Type ℓ}
           (A≃ : A₁ ≃ A₂) (B≃ : B₁ ≃ B₂) (C≃ : C₁ ≃ C₂)
           (f₁ : A₁ → B₁) (g₁ : A₁ → C₁)
           (f₂ : A₂ → B₂) (g₂ : A₂ → C₂)
           (id1 : (fst B≃) ∘ f₁ ≡ f₂ ∘ (fst A≃))
           (id2 : (fst C≃) ∘ g₁ ≡ g₂ ∘ (fst A≃))
   where
   F : Pushout f₁ g₁ → Pushout f₂ g₂
   F (inl x) = inl (fst B≃ x)
   F (inr x) = inr (fst C≃ x)
   F (push a i) =
     ((λ i → inl (funExt⁻ id1 a i))
      ∙∙ push (fst A≃ a)
      ∙∙ λ i → inr (sym (funExt⁻ id2 a) i)) i

   G : Pushout f₂ g₂ → Pushout f₁ g₁
   G (inl x) = inl (invEq B≃ x)
   G (inr x) = inr (invEq C≃ x)
   G (push a i) =
     ((λ i → inl ((sym (cong (invEq B≃) (funExt⁻ id1 (invEq A≃ a)
                    ∙ cong f₂ (secEq A≃ a)))
                    ∙ retEq B≃ (f₁ (invEq A≃ a))) i))
      ∙∙ push (invEq A≃ a)
      ∙∙ λ i → inr (((sym (retEq C≃ (g₁ (invEq A≃ a)))
                   ∙ (cong (invEq C≃) ((funExt⁻ id2 (invEq A≃ a)))))
                   ∙ cong (invEq C≃) (cong g₂ (secEq A≃ a))) i)) i


  abbrType₁ : {ℓ : Level} {A₁ B₁ C₁ A₂ B₂ C₂ : Type ℓ}
       (A≃ : A₁ ≃ A₂) (B≃ : B₁ ≃ B₂) (C≃ : C₁ ≃ C₂)
    → (f₁ : A₁ → B₁) (g₁ : A₁ → C₁)
       (f₂ : A₂ → B₂) (g₂ : A₂ → C₂)
    → (id1 : (fst B≃) ∘ f₁ ≡ f₂ ∘ (fst A≃))
       (id2 : (fst C≃) ∘ g₁ ≡ g₂ ∘ (fst A≃))
    → Type _
  abbrType₁ A≃ B≃ C≃ f₁ g₁ f₂ g₂ id1 id2 =
      ((x : _) → PushoutIso.F A≃ B≃ C≃ f₁ g₁ f₂ g₂ id1 id2
                   (PushoutIso.G A≃ B≃ C≃ f₁ g₁ f₂ g₂ id1 id2 x) ≡ x)
    × ((x : _) → PushoutIso.G A≃ B≃ C≃ f₁ g₁ f₂ g₂ id1 id2
                   (PushoutIso.F A≃ B≃ C≃ f₁ g₁ f₂ g₂ id1 id2 x) ≡ x)

  abbrType : {ℓ : Level} {A₁ B₁ C₁ A₂ B₂ C₂ : Type ℓ}
             (A≃ : A₁ ≃ A₂) (B≃ : B₁ ≃ B₂) (C≃ : C₁ ≃ C₂)
          → Type _
  abbrType {A₁ = A₁} {B₁ = B₁} {C₁ = C₁} {A₂ = A₂} {B₂ = B₂} {C₂ = C₂}
    A≃ B≃ C≃ =
    (f₁ : A₁ → B₁) (g₁ : A₁ → C₁)
    (f₂ : A₂ → B₂) (g₂ : A₂ → C₂)
    (id1 : (fst B≃) ∘ f₁ ≡ f₂ ∘ (fst A≃))
    (id2 : (fst C≃) ∘ g₁ ≡ g₂ ∘ (fst A≃))
    → abbrType₁ A≃ B≃ C≃ f₁ g₁ f₂ g₂ id1 id2

  F-G-cancel : {ℓ : Level} {A₁ B₁ C₁ A₂ B₂ C₂ : Type ℓ}
               (A≃ : A₁ ≃ A₂) (B≃ : B₁ ≃ B₂) (C≃ : C₁ ≃ C₂)
             → abbrType A≃ B≃ C≃
  F-G-cancel {A₁ = A₁} {B₁ = B₁} {C₁ = C₁} {A₂ = A₂} {B₂ = B₂} {C₂ = C₂} =
    EquivJ (λ A₁ A≃ → (B≃ : B₁ ≃ B₂) (C≃ : C₁ ≃ C₂) →
      abbrType A≃ B≃ C≃)
      (EquivJ (λ B₁ B≃ → (C≃ : C₁ ≃ C₂) →
      abbrType (idEquiv A₂) B≃ C≃)
        (EquivJ (λ C₁ C≃ → abbrType (idEquiv A₂) (idEquiv B₂) C≃)
          λ f₁ g₁ f₂ g₂
            → J (λ f₂ id1 → (id2 : g₁ ≡ g₂)
                          → abbrType₁ (idEquiv A₂) (idEquiv B₂) (idEquiv C₂)
                                    f₁ g₁ f₂ g₂ id1 id2)
                 (J (λ g₂ id2 → abbrType₁ (idEquiv A₂) (idEquiv B₂) (idEquiv C₂)
                                        f₁ g₁ f₁ g₂ refl id2)
                    (postJ f₁ g₁))))

    where
    postJ : (f₁ : A₂ → B₂) (g₁ : A₂ → C₂)
      → abbrType₁ (idEquiv A₂) (idEquiv B₂) (idEquiv C₂)
                 f₁ g₁ f₁ g₁ refl refl
    postJ f₁ g₁ = FF-GG , GG-FF
      where
      refl-lem : ∀ {ℓ} {A : Type ℓ} (x : A)
              → (refl {x = x} ∙ refl) ∙ refl ≡ refl
      refl-lem x = sym (rUnit _) ∙ sym (rUnit _)

      FF = PushoutIso.F (idEquiv A₂) (idEquiv B₂) (idEquiv C₂)
                        f₁ g₁ f₁ g₁ refl refl
      GG = PushoutIso.G (idEquiv A₂) (idEquiv B₂) (idEquiv C₂)
                        f₁ g₁ f₁ g₁ refl refl

      FF-GG : (x : Pushout f₁ g₁) → FF (GG x) ≡ x
      FF-GG (inl x) = refl
      FF-GG (inr x) = refl
      FF-GG (push a i) j = lem j i
        where
        lem : Path (Path (Pushout f₁ g₁) (inl (f₁ a)) (inr (g₁ a)))
                  (cong FF ((λ i → inl (((refl ∙ refl) ∙ (refl {x = f₁ a})) i ))
                        ∙∙ push {f = f₁} {g = g₁} a
                        ∙∙ λ i → inr (((refl ∙ refl) ∙ (refl {x = g₁ a})) i)))
                  (push a)
        lem = (λ i → cong FF ((λ j → inl (refl-lem (f₁ a) i j))
                           ∙∙ push a
                           ∙∙ λ j → inr (refl-lem (g₁ a) i j)))
          ∙∙ cong (cong FF) (sym (rUnit (push a)))
          ∙∙ sym (rUnit (push a))

      GG-FF : (x : _) → GG (FF x) ≡ x
      GG-FF (inl x) = refl
      GG-FF (inr x) = refl
      GG-FF (push a i) j = lem j i
        where
        lem : cong GG (refl ∙∙ push a ∙∙ refl) ≡ push a
        lem = cong (cong GG) (sym (rUnit (push a)))
          ∙∙ (λ i → ((λ j → inl (refl-lem (f₁ a) i j))
                   ∙∙ push a
                   ∙∙ λ j → inr (refl-lem (g₁ a) i j)))
          ∙∙ sym (rUnit (push a))

-- induced isomorphism of pushouts (see later def. pushoutIso/pushoutEquiv for a more universe polymorphic)
module _ {ℓ : Level} {A₁ B₁ C₁ A₂ B₂ C₂ : Type ℓ}
  (f₁ : A₁ → B₁) (g₁ : A₁ → C₁)
  (f₂ : A₂ → B₂) (g₂ : A₂ → C₂)
  (A≃ : A₁ ≃ A₂) (B≃ : B₁ ≃ B₂) (C≃ : C₁ ≃ C₂)
  (id1 : fst B≃ ∘ f₁ ≡ f₂ ∘ fst A≃)
  (id2 : fst C≃ ∘ g₁ ≡ g₂ ∘ fst A≃)
  where
  private
    module P = PushoutIso A≃ B≃ C≃ f₁ g₁ f₂ g₂ id1 id2
    l-r-cancel = F-G-cancel A≃ B≃ C≃ f₁ g₁ f₂ g₂ id1 id2

  pushoutIso' : Iso (Pushout f₁ g₁) (Pushout f₂ g₂)
  fun pushoutIso' = P.F
  inv pushoutIso' = P.G
  rightInv pushoutIso' = fst l-r-cancel
  leftInv pushoutIso' = snd l-r-cancel

  pushoutEquiv' : Pushout f₁ g₁ ≃ Pushout f₂ g₂
  pushoutEquiv' = isoToEquiv pushoutIso'

-- lift induces an equivalence on Pushouts
module _ {ℓ ℓ' ℓ'' : Level} (ℓ''' : Level)
  {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} (f : A → B) (g : A → C) where
  PushoutLevel  : Level
  PushoutLevel = ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓ'' ℓ'''))

  PushoutLift : Type PushoutLevel
  PushoutLift = Pushout {A = Lift {j = ℓ-max ℓ' (ℓ-max ℓ'' ℓ''')} A}
                        {B = Lift {j = ℓ-max ℓ (ℓ-max ℓ'' ℓ''')} B}
                        {C = Lift {j = ℓ-max ℓ (ℓ-max ℓ' ℓ''')} C}
                        (liftFun f)
                        (liftFun g)

  PushoutLiftIso : Iso (Pushout f g) PushoutLift
  Iso.fun PushoutLiftIso (inl x) = inl (lift x)
  Iso.fun PushoutLiftIso (inr x) = inr (lift x)
  Iso.fun PushoutLiftIso (push a i) = push (lift a) i
  Iso.inv PushoutLiftIso (inl (lift x)) = inl x
  Iso.inv PushoutLiftIso (inr (lift x)) = inr x
  Iso.inv PushoutLiftIso (push (lift a) i) = push a i
  Iso.rightInv PushoutLiftIso (inl (lift x)) = refl
  Iso.rightInv PushoutLiftIso (inr (lift x)) = refl
  Iso.rightInv PushoutLiftIso (push (lift a) i) = refl
  Iso.leftInv PushoutLiftIso (inl x) = refl
  Iso.leftInv PushoutLiftIso (inr x) = refl
  Iso.leftInv PushoutLiftIso (push a i) = refl

-- equivalence of pushouts with arbitrary univeses
module _ {ℓA₁ ℓB₁ ℓC₁ ℓA₂ ℓB₂ ℓC₂}
      {A₁ : Type ℓA₁} {B₁ : Type ℓB₁} {C₁ : Type ℓC₁}
      {A₂ : Type ℓA₂} {B₂ : Type ℓB₂} {C₂ : Type ℓC₂}
      (f₁ : A₁ → B₁) (g₁ : A₁ → C₁)
      (f₂ : A₂ → B₂) (g₂ : A₂ → C₂)
      (A≃ : A₁ ≃ A₂) (B≃ : B₁ ≃ B₂) (C≃ : C₁ ≃ C₂)
      (id1 : fst B≃ ∘ f₁ ≡ f₂ ∘ fst A≃)
      (id2 : fst C≃ ∘ g₁ ≡ g₂ ∘ fst A≃) where
  private
    ℓ* = ℓ-max ℓA₁ (ℓ-max ℓA₂ (ℓ-max ℓB₁ (ℓ-max ℓB₂ (ℓ-max ℓC₁ ℓC₂))))

    pushoutIso→ : Pushout f₁ g₁ → Pushout f₂ g₂
    pushoutIso→ (inl x) = inl (fst B≃ x)
    pushoutIso→ (inr x) = inr (fst C≃ x)
    pushoutIso→ (push a i) =
      ((λ i → inl (id1 i a)) ∙∙ push (fst A≃ a) ∙∙ λ i → inr (id2 (~ i) a)) i

    pushoutIso* : Iso (Pushout f₁ g₁) (Pushout f₂ g₂)
    pushoutIso* =
        compIso (PushoutLiftIso ℓ* f₁ g₁)
          (compIso (pushoutIso' _ _ _ _
            (Lift≃Lift A≃)
            (Lift≃Lift B≃)
            (Lift≃Lift C≃)
            (funExt (λ { (lift x) → cong lift (funExt⁻ id1 x)}))
            (funExt (λ { (lift x) → cong lift (funExt⁻ id2 x)})))
          (invIso (PushoutLiftIso ℓ* f₂ g₂)))

    pushoutIso→≡ : (x : _) → Iso.fun pushoutIso* x ≡ pushoutIso→ x
    pushoutIso→≡ (inl x) = refl
    pushoutIso→≡ (inr x) = refl
    pushoutIso→≡ (push a i) j =
      cong-∙∙ (Iso.inv (PushoutLiftIso ℓ* f₂ g₂))
            (λ i → inl (lift (id1 i a)))
            (push (lift (fst A≃ a)))
            (λ i → inr (lift (id2 (~ i) a))) j i

  pushoutIso : Iso (Pushout f₁ g₁) (Pushout f₂ g₂)
  fun pushoutIso = pushoutIso→
  inv pushoutIso = inv pushoutIso*
  rightInv pushoutIso x =
    sym (pushoutIso→≡ (inv pushoutIso* x)) ∙ rightInv pushoutIso* x
  leftInv pushoutIso x =
    cong (inv pushoutIso*) (sym (pushoutIso→≡ x)) ∙ leftInv pushoutIso* x

  pushoutEquiv : Pushout f₁ g₁ ≃ Pushout f₂ g₂
  pushoutEquiv = isoToEquiv pushoutIso

-- Pushouts commute with Σ
module _ {ℓ ℓ' ℓ'' ℓ'''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
  (f : A → B) (g : A → C) (X : Pushout f g → Type ℓ''') where
  open FlatteningLemma f g (X ∘ inl) (X ∘ inr) (λ a → substEquiv X (push a))

  PushoutΣL : Σ[ a ∈ A ] X (inl (f a)) → Σ[ b ∈ B ] X (inl b)
  PushoutΣL (a , x) = f a , x

  PushoutΣR : Σ[ a ∈ A ] X (inl (f a)) → Σ[ c ∈ C ] X (inr c)
  PushoutΣR (a , x) = g a , subst X (push a) x

  PushoutΣ : Type _
  PushoutΣ = Pushout PushoutΣL PushoutΣR

  repairLeft : (a : Pushout f g) → X a ≃ E a
  repairLeft (inl x) = idEquiv _
  repairLeft (inr x) = idEquiv _
  repairLeft (push a i) = help i
    where
    help : PathP (λ i → X (push a i) ≃ E (push a i)) (idEquiv _) (idEquiv _)
    help = ΣPathPProp (λ _ → isPropIsEquiv _)
                      (toPathP (funExt λ x →
                        transportRefl _ ∙ substSubst⁻ X (push a) x))

  ΣPushout≃PushoutΣ : Σ (Pushout f g) X ≃ PushoutΣ
  ΣPushout≃PushoutΣ =
    compEquiv (Σ-cong-equiv-snd repairLeft) flatten

module _ {C : Type ℓ} {B : Type ℓ'} where
  PushoutAlongEquiv→ : {A : Type ℓ}
    (e : A ≃ C) (f : A → B) → Pushout (fst e) f → B
  PushoutAlongEquiv→ e f (inl x) = f (invEq e x)
  PushoutAlongEquiv→ e f (inr x) = x
  PushoutAlongEquiv→ e f (push a i) = f (retEq e a i)

  private
    PushoutAlongEquiv→Cancel : {A : Type ℓ} (e : A ≃ C) (f : A → B)
      → retract (PushoutAlongEquiv→ e f) inr
    PushoutAlongEquiv→Cancel =
      EquivJ (λ A e → (f : A → B)
                    → retract (PushoutAlongEquiv→ e f) inr)
            λ f → λ { (inl x) → sym (push x)
                      ; (inr x) → refl
                      ; (push a i) j → push a (~ j ∨ i)}

  PushoutAlongEquiv : {A : Type ℓ} (e : A ≃ C) (f : A → B)
    → Iso (Pushout (fst e) f) B
  Iso.fun (PushoutAlongEquiv e f) = PushoutAlongEquiv→ e f
  Iso.inv (PushoutAlongEquiv e f) = inr
  Iso.rightInv (PushoutAlongEquiv e f) x = refl
  Iso.leftInv (PushoutAlongEquiv e f) = PushoutAlongEquiv→Cancel e f

module PushoutDistr {ℓ ℓ' ℓ'' ℓ''' : Level}
  {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} {D : Type ℓ'''}
  (f : B → A) (g : C → B) (h : C → D) where
  PushoutDistrFun : Pushout {C = Pushout g h} f inl → Pushout (f ∘ g) h
  PushoutDistrFun (inl x) = inl x
  PushoutDistrFun (inr (inl x)) = inl (f x)
  PushoutDistrFun (inr (inr x)) = inr x
  PushoutDistrFun (inr (push a i)) = push a i
  PushoutDistrFun (push a i) = inl (f a)

  PushoutDistrInv : Pushout (f ∘ g) h → Pushout {C = Pushout g h} f inl
  PushoutDistrInv (inl x) = inl x
  PushoutDistrInv (inr x) = inr (inr x)
  PushoutDistrInv (push c i) = (push (g c) ∙ λ j → inr (push c j)) i

  PushoutDistrIso : Iso (Pushout {C = Pushout g h} f inl) (Pushout (f ∘ g) h)
  fun PushoutDistrIso = PushoutDistrFun
  inv PushoutDistrIso = PushoutDistrInv
  rightInv PushoutDistrIso (inl x) = refl
  rightInv PushoutDistrIso (inr x) = refl
  rightInv PushoutDistrIso (push a i) j =
      (cong-∙ (fun PushoutDistrIso) (push (g a)) (λ j → inr (push a j))
    ∙ sym (lUnit _)) j i
  leftInv PushoutDistrIso (inl x) = refl
  leftInv PushoutDistrIso (inr (inl x)) = push x
  leftInv PushoutDistrIso (inr (inr x)) = refl
  leftInv PushoutDistrIso (inr (push a i)) j =
    compPath-filler' (push (g a)) (λ j → inr (push a j)) (~ j) i
  leftInv PushoutDistrIso (push a i) j = push a (i ∧ j)

PushoutEmptyFam : ¬ A → ¬ C
  → {f : A → B} {g : A → C}
  → Iso B (Pushout {A = A} {B = B} {C = C} f g)
fun (PushoutEmptyFam ¬A ¬C) = inl
inv (PushoutEmptyFam ¬A ¬C) (inl x) = x
inv (PushoutEmptyFam ¬A ¬C) (inr x) = ⊥.rec (¬C x)
inv (PushoutEmptyFam ¬A ¬C {f = f} {g = g}) (push a i) =
  ⊥.rec {A = f a ≡ ⊥.rec (¬C (g a))} (¬A a) i
rightInv (PushoutEmptyFam {A = A} {B = B} ¬A ¬C) (inl x) = refl
rightInv (PushoutEmptyFam {A = A} {B = B} ¬A ¬C) (inr x) = ⊥.rec (¬C x)
rightInv (PushoutEmptyFam {A = A} {B = B} ¬A ¬C {f = f} {g = g}) (push a i) j =
  ⊥.rec {A = Square (λ i →  inl (⊥.rec {A = f a ≡ ⊥.rec (¬C (g a))} (¬A a) i))
                     (push a) (λ _ → inl (f a)) (⊥.rec (¬C (g a)))}
         (¬A a) j i
leftInv (PushoutEmptyFam {A = A} {B = B} ¬A ¬C) x = refl

PushoutEmptyDomainIso : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
  → Iso (Pushout {A = ⊥} {B = A} {C = B} (λ()) (λ())) (A ⊎ B)
Iso.fun PushoutEmptyDomainIso (inl x) = inl x
Iso.fun PushoutEmptyDomainIso (inr x) = inr x
Iso.inv PushoutEmptyDomainIso (inl x) = inl x
Iso.inv PushoutEmptyDomainIso (inr x) = inr x
Iso.rightInv PushoutEmptyDomainIso (inl x) = refl
Iso.rightInv PushoutEmptyDomainIso (inr x) = refl
Iso.leftInv PushoutEmptyDomainIso (inl x) = refl
Iso.leftInv PushoutEmptyDomainIso (inr x) = refl

PushoutCompEquivIso : ∀ {ℓA ℓA' ℓB ℓB' ℓC}
  {A : Type ℓA} {A' : Type ℓA'} {B : Type ℓB} {B' : Type ℓB'}
  {C : Type ℓC}
  (e1 : A ≃ A') (e2 : B' ≃ B)
  (f : A' → B') (g : A → C)
  → Iso (Pushout (fst e2 ∘ f ∘ fst e1) g) (Pushout f (g ∘ invEq e1))
PushoutCompEquivIso {ℓA = ℓA} {ℓA'} {ℓB} {ℓB'} {ℓC} e1 e2 f g =
  compIso (pushoutIso _ _ _ _ LiftEquiv LiftEquiv LiftEquiv refl refl)
    (compIso (PushoutCompEquivIso' {ℓ = ℓ*} {ℓ*} {ℓ*}
      (liftEq ℓ* e1) (liftEq ℓ* e2) (liftFun f) (liftFun g))
      (invIso (pushoutIso _ _ _ _
               LiftEquiv LiftEquiv (LiftEquiv {ℓ' = ℓ*}) refl refl)))
  where
  ℓ* = ℓ-maxList (ℓA ∷ ℓA' ∷ ℓB ∷ ℓB' ∷ ℓC ∷ [])

  liftEq : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (ℓ* : Level)
    → A ≃ B → Lift {j = ℓ*} A ≃ Lift {j = ℓ*} B
  liftEq ℓ* e = compEquiv (invEquiv LiftEquiv) (compEquiv e LiftEquiv)

  PushoutCompEquivIso' : ∀ {ℓ ℓ' ℓ''} {A A' : Type ℓ} {B B' : Type ℓ'} {C : Type ℓ''}
    (e1 : A ≃ A') (e2 : B' ≃ B)
    (f : A' → B') (g : A → C)
    → Iso (Pushout (fst e2 ∘ f ∘ fst e1) g) (Pushout f (g ∘ invEq e1))
  PushoutCompEquivIso' {A = A} {A' = A'} {B} {B'} {C} =
    EquivJ (λ A e1 → (e2 : B' ≃ B) (f : A' → B') (g : A → C)
                   →  Iso (Pushout (fst e2 ∘ f ∘ fst e1) g)
                           (Pushout f (g ∘ invEq e1)))
     (EquivJ (λ B' e2 → (f : A' → B') (g : A' → C)
                   →  Iso (Pushout (fst e2 ∘ f) g)
                           (Pushout f g))
       λ f g → idIso)

-- Computation of cofibre of the quotient map B → B/A (where B/A
-- denotes the cofibre of some f : B → A)
module _ {A : Pointed ℓ} {B : Pointed ℓ'} (f : A →∙ B) where
  private
    open 3x3-span
    inst : 3x3-span
    A00 inst = Unit
    A02 inst = Unit
    A04 inst = Unit
    A20 inst = fst A
    A22 inst = Unit
    A24 inst = Unit
    A40 inst = fst B
    A42 inst = fst B
    A44 inst = Unit
    f10 inst = _
    f12 inst = _
    f14 inst = _
    f30 inst = fst f
    f32 inst = λ _ → pt B
    f34 inst = _
    f01 inst = _
    f21 inst = λ _ → pt A
    f41 inst = idfun (fst B)
    f03 inst = _
    f23 inst = _
    f43 inst = _
    H11 inst = (λ _ → refl)
    H13 inst = λ _ → refl
    H31 inst = λ _ → sym (snd f)
    H33 inst = λ _ → refl

    A□0≅cofib-f : Iso (A□0 inst) (cofib (fst f))
    A□0≅cofib-f = idIso

    A□2≅B : Iso (A□2 inst) (fst B)
    A□2≅B = PushoutAlongEquiv (idEquiv _) λ _ → pt B

    A□4≅Unit : Iso (A□4 inst) Unit
    A□4≅Unit = PushoutAlongEquiv (idEquiv _) λ _ → tt

    A0□≅Unit : Iso (A0□ inst) Unit
    A0□≅Unit = PushoutAlongEquiv (idEquiv _) λ _ → tt

    A2□≅A : Iso (A2□ inst) (fst A)
    A2□≅A = compIso (equivToIso (invEquiv (symPushout _ _)))
                    (PushoutAlongEquiv (idEquiv _) λ _ → pt A)

    A4□≅Unit : Iso (A4□ inst) Unit
    A4□≅Unit = PushoutAlongEquiv (idEquiv _) λ _ → tt

    A□○≅cofibInr : Iso (A□○ inst) (cofib {B = cofib (fst f)} inr)
    A□○≅cofibInr = compIso (invIso (equivToIso (symPushout _ _)))
                           (pushoutIso _ _ _ _
                             (isoToEquiv A□2≅B)
                             (isoToEquiv A□4≅Unit)
                             (isoToEquiv A□0≅cofib-f)
                             refl (funExt λ x
                               → cong (A□0≅cofib-f .Iso.fun ∘ f□1 inst)
                                       (sym (Iso.leftInv A□2≅B x))))

    A○□≅ : Iso (A○□ inst) (Susp (typ A))
    A○□≅ =
      compIso
        (pushoutIso _ _ _ _
          (isoToEquiv A2□≅A)
          (isoToEquiv A0□≅Unit)
          (isoToEquiv A4□≅Unit)
          refl refl)
        PushoutSuspIsoSusp

  Iso-cofibInr-Susp : Iso (cofib {B = cofib (fst f)} inr)
                          (Susp (typ A))
  Iso-cofibInr-Susp =
    compIso (compIso (invIso A□○≅cofibInr)
      (3x3-Iso inst)) A○□≅

-- Commutative squares and pushout squares
module _ {ℓ₀ ℓ₂ ℓ₄ ℓP : Level} where
  private
    ℓ* = ℓ-maxList (ℓ₀ ∷ ℓ₂ ∷ ℓ₄ ∷ ℓP ∷ [])

  record  commSquare : Type (ℓ-suc ℓ*) where
    open 3-span
    field
      sp : 3-span {ℓ₀} {ℓ₂} {ℓ₄}
      P : Type ℓP
      inlP : A0 sp → P
      inrP : A4 sp → P
      comm : inlP ∘ f1 sp ≡ inrP ∘ f3 sp

  open commSquare

  Pushout→commSquare : (sk : commSquare) → spanPushout (sp sk) → P sk
  Pushout→commSquare sk (inl x) = inlP sk x
  Pushout→commSquare sk (inr x) = inrP sk x
  Pushout→commSquare sk (push a i) = comm sk i a

  isPushoutSquare : commSquare → Type _
  isPushoutSquare sk = isEquiv (Pushout→commSquare sk)

  PushoutSquare : Type (ℓ-suc ℓ*)
  PushoutSquare = Σ commSquare isPushoutSquare

module _ {ℓ₀ ℓ₂ ℓ₄ ℓP ℓP' : Level}
  {P' : Type ℓP'} where
  open commSquare
  extendCommSquare : (sk : commSquare {ℓ₀} {ℓ₂} {ℓ₄} {ℓP})
    → (sk .P → P') → commSquare
  extendCommSquare sk f .sp = sk .sp
  extendCommSquare sk f .P = P'
  extendCommSquare sk f .inlP = f ∘ sk .inlP
  extendCommSquare sk f .inrP = f ∘ sk .inrP
  extendCommSquare sk f .comm = cong (f ∘_) (sk .comm)


  extendPushoutSquare : (sk : PushoutSquare {ℓ₀} {ℓ₂} {ℓ₄} {ℓP})
    → (e : sk .fst .P ≃ P') → PushoutSquare
  extendPushoutSquare sk e = (extendCommSquare (sk .fst) (e .fst) ,
    subst isEquiv H (compEquiv (_ , sk .snd) e .snd))
    where
      H : e .fst ∘ _ ≡ _
      H = funExt λ
        { (inl x) → refl
        ; (inr x) → refl
        ; (push a i) → refl }

-- Pushout itself fits into a pushout square
pushoutToSquare : 3-span {ℓ} {ℓ'} {ℓ''} → PushoutSquare
pushoutToSquare spn .fst = cSq
  where
  open commSquare
  cSq : commSquare
  cSq .sp = spn
  cSq .P = spanPushout spn
  cSq .inlP = inl
  cSq .inrP = inr
  cSq .comm = funExt push
pushoutToSquare sp .snd =
  subst isEquiv (funExt H) (idIsEquiv _)
  where
  H : ∀ p → p ≡ Pushout→commSquare _ p
  H (inl x) = refl
  H (inr x) = refl
  H (push a i) = refl

-- Rotations of commutative squares and pushout squares
module _ {ℓ₀ ℓ₂ ℓ₄ ℓP : Level} where
  open commSquare
  open 3-span

  rotateCommSquare : commSquare {ℓ₀} {ℓ₂} {ℓ₄} {ℓP} → commSquare {ℓ₄} {ℓ₂} {ℓ₀} {ℓP}
  A0 (sp (rotateCommSquare sq)) = A4 (sp sq)
  A2 (sp (rotateCommSquare sq)) = A2 (sp sq)
  A4 (sp (rotateCommSquare sq)) = A0 (sp sq)
  f1 (sp (rotateCommSquare sq)) = f3 (sp sq)
  f3 (sp (rotateCommSquare sq)) = f1 (sp sq)
  P (rotateCommSquare sq) = P sq
  inlP (rotateCommSquare sq) = inrP sq
  inrP (rotateCommSquare sq) = inlP sq
  comm (rotateCommSquare sq) = sym (comm sq)

  rotatePushoutSquare : PushoutSquare {ℓ₀} {ℓ₂} {ℓ₄} {ℓP}
                     → PushoutSquare {ℓ₄} {ℓ₂} {ℓ₀} {ℓP}
  fst (rotatePushoutSquare (sq , eq)) = rotateCommSquare sq
  snd (rotatePushoutSquare (sq , eq)) =
    subst isEquiv (funExt lem) (compEquiv (symPushout _ _) (_ , eq) .snd)
    where
    lem : (x : _) → Pushout→commSquare sq (symPushout _ _ .fst x)
                  ≡ Pushout→commSquare (rotateCommSquare sq) x
    lem (inl x) = refl
    lem (inr x) = refl
    lem (push a i) = refl


-- Pushout pasting lemma:
{- Given a diagram consisting of two
commuting squares where the top square is a pushout:

A2 -—f3-→ A4
 ∣           ∣
f1         inrP
 ↓       ⌜  ↓
A0 -—inlP→ P
 |          |
 f          h
 ↓          ↓
 A -—-g-—→ B

The bottom square is a pushout square iff the outer rectangle is
a pushout square.
-}

module PushoutPasteDown {ℓ₀ ℓ₂ ℓ₄ ℓP ℓA ℓB : Level}
  (SQ : PushoutSquare {ℓ₀} {ℓ₂} {ℓ₄} {ℓP})
  {A : Type ℓA} {B : Type ℓB}
  (f : 3-span.A0 (commSquare.sp (fst SQ)) → A)
  (g : A → B) (h : commSquare.P (fst SQ) → B)
  (com : g ∘ f ≡ h ∘ commSquare.inlP (fst SQ))
  where
  private
    sq = fst SQ
    isP = snd SQ
    ℓ* = ℓ-maxList (ℓ₀ ∷ ℓ₂ ∷ ℓ₄ ∷ ℓP ∷ [])

  open commSquare sq
  open 3-span sp

  bottomSquare : commSquare
  3-span.A0 (commSquare.sp bottomSquare) = A
  3-span.A2 (commSquare.sp bottomSquare) = A0
  3-span.A4 (commSquare.sp bottomSquare) = P
  3-span.f1 (commSquare.sp bottomSquare) = f
  3-span.f3 (commSquare.sp bottomSquare) = inlP
  commSquare.P bottomSquare = B
  commSquare.inlP bottomSquare = g
  commSquare.inrP bottomSquare = h
  commSquare.comm bottomSquare = com

  totSquare : commSquare
  3-span.A0 (commSquare.sp totSquare) = A
  3-span.A2 (commSquare.sp totSquare) = A2
  3-span.A4 (commSquare.sp totSquare) = A4
  3-span.f1 (commSquare.sp totSquare) = f ∘ f1
  3-span.f3 (commSquare.sp totSquare) = f3
  commSquare.P totSquare = B
  commSquare.inlP totSquare = g
  commSquare.inrP totSquare = h ∘ inrP
  commSquare.comm totSquare =
    funExt λ x → funExt⁻ com (f1 x) ∙ cong h (funExt⁻ comm x)

  private
    P' : Type _
    P' = Pushout f1 f3

    Iso-P'-P : P' ≃ P
    Iso-P'-P = _ , isP

    P'≃P = equiv→HAEquiv Iso-P'-P

    B'bot = Pushout {C = P'} f inl

    B'bot→BBot : B'bot → Pushout {C = P} f inlP
    B'bot→BBot (inl x) = inl x
    B'bot→BBot (inr x) = inr (fst Iso-P'-P x)
    B'bot→BBot (push a i) = push a i

    Bbot→B'bot : Pushout {C = P} f inlP → B'bot
    Bbot→B'bot (inl x) = inl x
    Bbot→B'bot (inr x) = inr (invEq Iso-P'-P x)
    Bbot→B'bot (push a i) =
      (push a ∙ λ i → inr (isHAEquiv.linv (P'≃P .snd) (inl a) (~ i))) i

    Iso-B'bot-Bbot : Iso B'bot (Pushout {C = P} f inlP)
    fun Iso-B'bot-Bbot = B'bot→BBot
    inv Iso-B'bot-Bbot = Bbot→B'bot
    rightInv Iso-B'bot-Bbot (inl x) = refl
    rightInv Iso-B'bot-Bbot (inr x) i = inr (isHAEquiv.rinv (P'≃P .snd) x i)
    rightInv Iso-B'bot-Bbot (push a i) j = help j i
      where
      help : Square
               (cong B'bot→BBot
                (push a ∙ λ i → inr (isHAEquiv.linv (P'≃P .snd) (inl a) (~ i))))
               (push a)
               refl
               λ i → inr (isHAEquiv.rinv (P'≃P .snd) (inlP a) i)
      help = flipSquare ((λ i j → B'bot→BBot (compPath-filler (push a)
              (λ i → inr (isHAEquiv.linv (P'≃P .snd) (inl a) (~ i))) (~ j) i))
           ▷ λ j i → inr (isHAEquiv.com (P'≃P .snd) (inl a) j i))
    leftInv Iso-B'bot-Bbot (inl x) = refl
    leftInv Iso-B'bot-Bbot (inr x) i = inr (isHAEquiv.linv (P'≃P .snd) x i)
    leftInv Iso-B'bot-Bbot (push a i) j =
      compPath-filler (push a)
        (λ i → inr (isHAEquiv.linv (P'≃P .snd) (inl a) (~ i))) (~ j) i

    B'tot : Type _
    B'tot = Pushout (f ∘ f1) f3

    B'bot→B'tot : B'bot → B'tot
    B'bot→B'tot (inl x) = inl x
    B'bot→B'tot (inr (inl x)) = inl (f x)
    B'bot→B'tot (inr (inr x)) = inr x
    B'bot→B'tot (inr (push a i)) = push a i
    B'bot→B'tot (push a i) = inl (f a)

    B'tot→B'bot : B'tot → B'bot
    B'tot→B'bot (inl x) = inl x
    B'tot→B'bot (inr x) = inr (inr x)
    B'tot→B'bot (push a i) = (push (f1 a) ∙ λ i → inr (push a i)) i

    Iso-B'bot→B'tot : Iso B'bot B'tot
    Iso.fun Iso-B'bot→B'tot = B'bot→B'tot
    Iso.inv Iso-B'bot→B'tot = B'tot→B'bot
    Iso.rightInv Iso-B'bot→B'tot (inl x) = refl
    Iso.rightInv Iso-B'bot→B'tot (inr x) = refl
    Iso.rightInv Iso-B'bot→B'tot (push a i) j =
       (cong-∙ B'bot→B'tot (push (f1 a)) (λ i → inr (push a i))
      ∙ sym (lUnit _)) j i
    Iso.leftInv Iso-B'bot→B'tot (inl x) = refl
    Iso.leftInv Iso-B'bot→B'tot (inr (inl x)) = push x
    Iso.leftInv Iso-B'bot→B'tot (inr (inr x)) = refl
    Iso.leftInv Iso-B'bot→B'tot (inr (push a i)) j =
      compPath-filler' (push (f1 a)) (λ i → inr (push a i)) (~ j) i
    Iso.leftInv Iso-B'bot→B'tot (push a i) j = push a (i ∧ j)

    main' : Iso (spanPushout (commSquare.sp bottomSquare)) B'tot
    main' = compIso (invIso Iso-B'bot-Bbot) (Iso-B'bot→B'tot)

    mainInv∘ : (x : _) → Pushout→commSquare bottomSquare (main' .inv x)
                        ≡ Pushout→commSquare totSquare x
    mainInv∘ (inl x) = refl
    mainInv∘ (inr x) = refl
    mainInv∘ (push a i) j = help j i
      where
      help : cong (Pushout→commSquare bottomSquare)
                  (cong (Iso.fun Iso-B'bot-Bbot) (push (f1 a) ∙ (λ i → inr (push a i))))
          ≡ funExt⁻ com (f1 a) ∙ cong h (funExt⁻ comm a)
      help = cong (cong (Pushout→commSquare bottomSquare))
                  (cong-∙ (Iso.fun Iso-B'bot-Bbot) (push (f1 a)) (λ i → inr (push a i)))
                ∙ cong-∙ (Pushout→commSquare bottomSquare)
                         (push (3-span.f1 (commSquare.sp sq) a))
                         (λ i → inr (commSquare.comm sq i a))

  isPushoutBottomSquare→isPushoutTotSquare :
    isPushoutSquare bottomSquare → isPushoutSquare totSquare
  isPushoutBottomSquare→isPushoutTotSquare eq =
    subst isEquiv (funExt mainInv∘) (isoToEquiv main .snd)
    where
    main : Iso (spanPushout (commSquare.sp totSquare)) B
    main = compIso (invIso main') (equivToIso (_ , eq))

  isPushoutTotSquare→isPushoutBottomSquare :
    isPushoutSquare totSquare → isPushoutSquare bottomSquare
  isPushoutTotSquare→isPushoutBottomSquare eq =
    subst isEquiv (funExt coh)
      (snd (isoToEquiv main))
    where

    main : Iso (spanPushout (commSquare.sp bottomSquare)) B
    main = compIso
            (compIso (invIso Iso-B'bot-Bbot) (Iso-B'bot→B'tot))
            (equivToIso (_ , eq))

    coh : (x : spanPushout (commSquare.sp bottomSquare)) →
          main .fun x ≡ Pushout→commSquare bottomSquare x
    coh x = sym (secEq (_ , eq) (fun main x))
      ∙∙ sym (mainInv∘ (invEq (_ , eq) (Iso.fun main x)))
      ∙∙ cong (Pushout→commSquare bottomSquare) (Iso.leftInv main x)

-- Pushout pasting lemma, alternative version:
{- Given a diagram consisting of two
commuting squares where the left square is a pushout:

A2 -—f3-→ A4 -—-f--→ A
 ∣           ∣          ∣
f1         inrP        g
 ↓       ⌜  ↓          ↓
A0 -—inlP→ P -—-h--→ B

The right square is a pushout square iff the outer rectangle is
a pushout square.
-}
module PushoutPasteLeft {ℓ₀ ℓ₂ ℓ₄ ℓP ℓA ℓB : Level}
  (SQ : PushoutSquare {ℓ₀} {ℓ₂} {ℓ₄} {ℓP})
  {A : Type ℓA} {B : Type ℓB}
  (f : 3-span.A4 (commSquare.sp (fst SQ)) → A)
  (g : A → B) (h : commSquare.P (fst SQ) → B)
  (com : h ∘ commSquare.inrP (fst SQ) ≡ g ∘ f)
  where

  private
    sq = fst SQ
    isP = snd SQ
    ℓ* = ℓ-maxList (ℓ₀ ∷ ℓ₂ ∷ ℓ₄ ∷ ℓP ∷ [])

  open commSquare sq
  open 3-span sp

  rightSquare : commSquare
  3-span.A0 (commSquare.sp rightSquare) = P
  3-span.A2 (commSquare.sp rightSquare) = A4
  3-span.A4 (commSquare.sp rightSquare) = A
  3-span.f1 (commSquare.sp rightSquare) = inrP
  3-span.f3 (commSquare.sp rightSquare) = f
  commSquare.P rightSquare = B
  commSquare.inlP rightSquare = h
  commSquare.inrP rightSquare = g
  commSquare.comm rightSquare = com

  totSquare : commSquare
  3-span.A0 (commSquare.sp totSquare) = A0
  3-span.A2 (commSquare.sp totSquare) = A2
  3-span.A4 (commSquare.sp totSquare) = A
  3-span.f1 (commSquare.sp totSquare) = f1
  3-span.f3 (commSquare.sp totSquare) = f ∘ f3
  commSquare.P totSquare = B
  commSquare.inlP totSquare = h ∘ inlP
  commSquare.inrP totSquare = g
  commSquare.comm totSquare = funExt λ x →
    sym (sym (funExt⁻ com (f3 x)) ∙ cong h (sym (funExt⁻ comm x)))


  module M = PushoutPasteDown (rotatePushoutSquare SQ) f g h (sym com)

  isPushoutRightSquare→isPushoutTotSquare :
    isPushoutSquare rightSquare → isPushoutSquare totSquare
  isPushoutRightSquare→isPushoutTotSquare e = rotatePushoutSquare (_ , help) .snd
    where
    help : isPushoutSquare M.totSquare
    help = M.isPushoutBottomSquare→isPushoutTotSquare (rotatePushoutSquare (_ , e) .snd)

  isPushoutTotSquare→isPushoutRightSquare :
    isPushoutSquare totSquare → isPushoutSquare rightSquare
  isPushoutTotSquare→isPushoutRightSquare e = rotatePushoutSquare (_ , help) .snd
    where
    help = M.isPushoutTotSquare→isPushoutBottomSquare (rotatePushoutSquare (_ , e) .snd)

LiftPushoutIso : (ℓP : Level) {f : A → B} {g : A → C}
  → Iso (Pushout (liftFun {ℓ'' = ℓP} {ℓ''' = ℓP} f)
                  (liftFun {ℓ'' = ℓP} {ℓ''' = ℓP} g))
         (Lift {j = ℓP} (Pushout f g))
fun (LiftPushoutIso ℓP) (inl (lift x)) = lift (inl x)
fun (LiftPushoutIso ℓP) (inr (lift x)) = lift (inr x)
fun (LiftPushoutIso ℓP) (push (lift a) i) = lift (push a i)
inv (LiftPushoutIso ℓP) (lift (inl x)) = inl (lift x)
inv (LiftPushoutIso ℓP) (lift (inr x)) = inr (lift x)
inv (LiftPushoutIso ℓP) (lift (push a i)) = push (lift a) i
rightInv (LiftPushoutIso ℓP) (lift (inl x)) = refl
rightInv (LiftPushoutIso ℓP) (lift (inr x)) = refl
rightInv (LiftPushoutIso ℓP) (lift (push a i)) = refl
leftInv (LiftPushoutIso ℓP) (inl (lift x)) = refl
leftInv (LiftPushoutIso ℓP) (inr (lift x)) = refl
leftInv (LiftPushoutIso ℓP) (push (lift a) i) = refl

{-# OPTIONS --safe #-}
module Cubical.Homotopy.Serre.LastMinuteLemmas.SuspLemmas where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Data.Nat

open import Cubical.HITs.Pushout
open import Cubical.HITs.Wedge
open import Cubical.HITs.Susp

private
  variable
    ℓ : Level

Susp∙^ : ℕ → Pointed ℓ → Pointed ℓ
Susp∙^ n x .fst = Susp^ n (typ x)
Susp∙^ zero x .snd = pt x
Susp∙^ (suc n) x .snd = Susp∙^ n (Susp∙ (typ x)) .snd

Susp^Fun : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B)
  (n : ℕ) → Susp^ n A → Susp^ n B
Susp^Fun f zero = f
Susp^Fun f (suc n) = Susp^Fun (suspFun f) n

Susp^Fun∙ : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} (f : A →∙ B)
  (n : ℕ) → Susp∙^ n A →∙ Susp∙^ n B
fst (Susp^Fun∙ f n) = Susp^Fun (fst f) n
snd (Susp^Fun∙ f zero) = snd f
snd (Susp^Fun∙ f (suc n)) = Susp^Fun∙ (suspFun∙ (fst f)) n .snd

Susp^Equiv : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A ≃ B)
  (n : ℕ) → Susp^ n A ≃ Susp^ n B
Susp^Equiv f n .fst = Susp^Fun (fst f) n
Susp^Equiv f zero .snd = snd f
Susp^Equiv f (suc n) .snd =
  Susp^Equiv (isoToEquiv (congSuspIso (equivToIso f))) n .snd

Susp^Equiv∙ : {A B : Pointed ℓ} (n : ℕ)
  → A ≃∙ B →  Susp∙^ n A ≃∙ Susp∙^ n B
Susp^Equiv∙ n e .fst = Susp^Equiv (fst e) n
Susp^Equiv∙ n e .snd = Susp^Fun∙ (≃∙map e) n .snd

Susp^-comm-Iso : (n : ℕ) (X : Type ℓ)
  → Iso (Susp^ (1 + n) X) (Susp (Susp^ n X))
Susp^-comm-Iso zero X = idIso
Susp^-comm-Iso (suc n) X = Susp^-comm-Iso n (Susp X)

Susp^-comm-Equiv∙ : (n : ℕ) (X : Pointed ℓ)
  → (Susp∙^ (1 + n) X) ≃∙ (Susp∙ (Susp^ n (typ X)))
Susp^-comm-Equiv∙ n X .fst = isoToEquiv (Susp^-comm-Iso n (typ X))
Susp^-comm-Equiv∙ zero X .snd = refl
Susp^-comm-Equiv∙ (suc n) X .snd =
  Susp^-comm-Equiv∙ n (Susp∙ (typ X)) .snd

Susp^-comm : (n : ℕ) (X : Type ℓ) → Susp^ (1 + n) X
                                   ≡ Susp (Susp^ n X)
Susp^-comm zero X = refl
Susp^-comm (suc n) X = Susp^-comm n (Susp X)

-- Move to Cubical.HITs.Susp.Properties
module _ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
         {f : A → B} {g : A → C} where
  private
    F : (a : A) (i j k : I) → Pushout (suspFun f) (suspFun g)
    F a i j k = hfill (λ k →
      λ{(i = i0) → inl (merid (f a) j)
      ; (i = i1) → doubleCompPath-filler (push north)
                      (λ i → inr (merid (g a) i))
                      (sym (push south)) k j
      ; (j = i0) → push north (~ k ∧ i)
      ; (j = i1) → push south (~ k ∧ i)})
            (inS (push (merid a j) i)) k

  SuspPushout→PushoutSusp : Susp (Pushout f g) → Pushout (suspFun f) (suspFun g)
  SuspPushout→PushoutSusp north = inl north
  SuspPushout→PushoutSusp south = inl south
  SuspPushout→PushoutSusp (merid (inl x) i) = inl (merid x i)
  SuspPushout→PushoutSusp (merid (inr x) i) =
    (push north ∙∙ (λ i → inr (merid x i)) ∙∙ sym (push south)) i
  SuspPushout→PushoutSusp (merid (push a i) j) = F a i j i1

  PushoutSusp→SuspPushout : Pushout (suspFun f) (suspFun g) → Susp (Pushout f g)
  PushoutSusp→SuspPushout (inl x) = suspFun inl x
  PushoutSusp→SuspPushout (inr x) = suspFun inr x
  PushoutSusp→SuspPushout (push north i) = north
  PushoutSusp→SuspPushout (push south i) = south
  PushoutSusp→SuspPushout (push (merid a i) j) = merid (push a j) i

  SuspCommPushoutIso : Iso (Susp (Pushout f g))
                           (Pushout (suspFun f) (suspFun g))
  SuspCommPushoutIso .Iso.fun = SuspPushout→PushoutSusp
  SuspCommPushoutIso .Iso.inv = PushoutSusp→SuspPushout
  SuspCommPushoutIso .Iso.sec (inl north) = refl
  SuspCommPushoutIso .Iso.sec (inl south) = refl
  SuspCommPushoutIso .Iso.sec (inl (merid a i)) = refl
  SuspCommPushoutIso .Iso.sec (inr north) = push north
  SuspCommPushoutIso .Iso.sec (inr south) = push south
  SuspCommPushoutIso .Iso.sec (inr (merid a i)) j =
    doubleCompPath-filler (push north)
                          (λ i → inr (merid a i))
                          (sym (push south)) (~ j) i
  SuspCommPushoutIso .Iso.sec (push north i) j = push north (i ∧ j)
  SuspCommPushoutIso .Iso.sec (push south i) j = push south (i ∧ j)
  SuspCommPushoutIso .Iso.sec (push (merid a i) j) k =
    hcomp (λ r →
      λ{(i = i0) → push north ((k ∨ ~ r) ∧ j)
      ; (i = i1) → push south ((k ∨ ~ r) ∧ j)
      ; (j = i0) → inl (merid (f a) i)
      ; (j = i1) → doubleCompPath-filler (push north)
                      (λ i → inr (merid (g a) i))
                      (sym (push south)) (~ k ∧ r) i
      ; (k = i1) → push (merid a i) j})
      (push (merid a i) j)
  SuspCommPushoutIso .Iso.ret north = refl
  SuspCommPushoutIso .Iso.ret south = refl
  SuspCommPushoutIso .Iso.ret (merid (inl x) i) = refl
  SuspCommPushoutIso .Iso.ret (merid (inr x) i) j =
    PushoutSusp→SuspPushout
      (doubleCompPath-filler (push north)
                          (λ i → inr (merid x i))
                          (sym (push south)) (~ j) i)
  SuspCommPushoutIso .Iso.ret (merid (push a j) i) k =
    hcomp (λ r →
      λ{(i = i0) → north
      ; (i = i1) → south
      ; (j = i0) → merid (inl (f a)) i
      ; (j = i1) → PushoutSusp→SuspPushout
                   (doubleCompPath-filler (push north)
                          (λ i → inr (merid (g a) i))
                          (sym (push south)) (~ k ∧ r) i)
      ; (k = i0) → PushoutSusp→SuspPushout (F a j i r)
      ; (k = i1) → merid (push a j) i})
      (merid (push a j) i)

-- Move to Cubical.HITs.Susp.Properties
Iso-SuspUnit-Unit : Iso (Susp Unit) Unit
Iso-SuspUnit-Unit .Iso.fun x = tt
Iso-SuspUnit-Unit .Iso.inv x = north
Iso-SuspUnit-Unit .Iso.sec tt = refl
Iso-SuspUnit-Unit .Iso.ret north = refl
Iso-SuspUnit-Unit .Iso.ret south = merid tt
Iso-SuspUnit-Unit .Iso.ret (merid a i) j = merid tt (i ∧ j)

-- Move to Cubical.HITs.Wedge.Properties
⋁Iso : ∀ {ℓ ℓ' ℓ'' ℓ'''} {A : Pointed ℓ} {B : Pointed ℓ'}
  {C : Pointed ℓ''} {D : Pointed ℓ'''} (e : A ≃∙ C) (e' : B ≃∙ D)
  → Iso (A ⋁ B) (C ⋁ D)
⋁Iso e e' = pushoutIso _ _ _ _
  (idEquiv Unit) (fst e) (fst e')
    (funExt (λ x → snd e))
    (funExt (λ x → snd e'))

Iso-⋁Susp-Susp⋁ : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'}
  → Iso (Susp (A ⋁ B)) (Susp∙ (typ A) ⋁ Susp∙ (typ B))
Iso-⋁Susp-Susp⋁ {A = A} {B} =
  compIso SuspCommPushoutIso
    (pushoutIso _ _ _ _
      (isoToEquiv Iso-SuspUnit-Unit) (idEquiv _) (idEquiv _)
      (funExt (λ { north → refl ; south → sym (merid (pt A))
                ; (merid a i) j → merid (pt A) (~ j ∧ i)}))
      (funExt (λ { north → refl ; south → sym (merid (pt B))
                ; (merid a i) j → merid (pt B) (~ j ∧ i)})))

⋁Susp≃∙Susp⋁ : (X Y : Pointed ℓ)
  → Susp∙ (X ⋁ Y) ≃∙ (Susp∙ (typ X) ⋁∙ₗ Susp∙ (typ Y))
⋁Susp≃∙Susp⋁ X Y .fst = isoToEquiv Iso-⋁Susp-Susp⋁
⋁Susp≃∙Susp⋁ X Y .snd = refl

⋁Susp^≃∙Susp^⋁ : (X Y : Pointed ℓ) (n : ℕ)
  → Susp∙^ n (X ⋁∙ₗ Y) ≃∙ (Susp∙^ n X ⋁∙ₗ Susp∙^ n Y)
⋁Susp^≃∙Susp^⋁ X Y zero = idEquiv∙ _
⋁Susp^≃∙Susp^⋁ X Y (suc n) =
  compEquiv∙ (Susp^Equiv∙ n (⋁Susp≃∙Susp⋁ X Y))
             (⋁Susp^≃∙Susp^⋁ (Susp∙ (typ X)) (Susp∙ (typ Y)) n)


-- Move to Cubical.Homotopy.Group
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Homotopy.Group.Base
open import Cubical.Homotopy.Loopspace

GrIso-πΩ^-π : ∀ {ℓ} {A : Pointed ℓ} (n m : ℕ)
          → GroupIso (πGr n ((Ω^ m) A)) (πGr (m + n) A)
GrIso-πΩ^-π n zero = idGroupIso
GrIso-πΩ^-π {A = A} n (suc m) =
  compGroupIso (GroupEquiv→GroupIso (πIso (isoToEquiv (flipΩIso m) , lem m) n))
    (compGroupIso (GrIso-πΩ^-π n m)
      (GrIso-πΩ-π (m + n)))
  where
  lem : (m : ℕ) → Iso.fun (flipΩIso {A = A} m) refl ≡ pt ((Ω^ m) (Ω A))
  lem zero = transportRefl refl
  lem (suc m) = flipΩrefl m

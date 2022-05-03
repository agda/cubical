{-# OPTIONS --safe #-}
module Cubical.HITs.Pushout.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Data.Unit
open import Cubical.Data.Sigma

open import Cubical.HITs.Susp.Base

data Pushout {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
             (f : A → B) (g : A → C) : Type (ℓ-max ℓ (ℓ-max ℓ' ℓ'')) where
  inl : B → Pushout f g
  inr : C → Pushout f g
  push : (a : A) → inl (f a) ≡ inr (g a)

-- cofiber (equivalent to Cone in Cubical.HITs.MappingCones.Base)
cofib : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B) → Type _
cofib f = Pushout (λ _ → tt) f

cfcod : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B) → B → cofib f
cfcod f = inr

-- Suspension defined as a pushout

PushoutSusp : ∀ {ℓ} (A : Type ℓ) → Type ℓ
PushoutSusp A = Pushout {A = A} {B = Unit} {C = Unit} (λ _ → tt) (λ _ → tt)

PushoutSusp→Susp : ∀ {ℓ} {A : Type ℓ} → PushoutSusp A → Susp A
PushoutSusp→Susp (inl _) = north
PushoutSusp→Susp (inr _) = south
PushoutSusp→Susp (push a i) = merid a i

Susp→PushoutSusp : ∀ {ℓ} {A : Type ℓ} → Susp A → PushoutSusp A
Susp→PushoutSusp north = inl tt
Susp→PushoutSusp south = inr tt
Susp→PushoutSusp (merid a i) = push a i

Susp→PushoutSusp→Susp : ∀ {ℓ} {A : Type ℓ} (x : Susp A) →
                        PushoutSusp→Susp (Susp→PushoutSusp x) ≡ x
Susp→PushoutSusp→Susp north = refl
Susp→PushoutSusp→Susp south = refl
Susp→PushoutSusp→Susp (merid _ _) = refl

PushoutSusp→Susp→PushoutSusp : ∀ {ℓ} {A : Type ℓ} (x : PushoutSusp A) →
                               Susp→PushoutSusp (PushoutSusp→Susp x) ≡ x
PushoutSusp→Susp→PushoutSusp (inl _) = refl
PushoutSusp→Susp→PushoutSusp (inr _) = refl
PushoutSusp→Susp→PushoutSusp (push _ _) = refl

PushoutSuspIsoSusp : ∀ {ℓ} {A : Type ℓ} → Iso (PushoutSusp A) (Susp A)
Iso.fun PushoutSuspIsoSusp = PushoutSusp→Susp
Iso.inv PushoutSuspIsoSusp = Susp→PushoutSusp
Iso.rightInv PushoutSuspIsoSusp = Susp→PushoutSusp→Susp
Iso.leftInv PushoutSuspIsoSusp = PushoutSusp→Susp→PushoutSusp


PushoutSusp≃Susp : ∀ {ℓ} {A : Type ℓ} → PushoutSusp A ≃ Susp A
PushoutSusp≃Susp = isoToEquiv PushoutSuspIsoSusp

PushoutSusp≡Susp : ∀ {ℓ} {A : Type ℓ} → PushoutSusp A ≡ Susp A
PushoutSusp≡Susp = isoToPath PushoutSuspIsoSusp

-- Generalised pushout, used in e.g. BlakersMassey
data PushoutGen {ℓ₁ ℓ₂ ℓ₃ : Level} {X : Type ℓ₁} {Y : Type ℓ₂}
                (Q : X → Y → Type ℓ₃) : Type (ℓ-max (ℓ-max ℓ₁ ℓ₂) ℓ₃)
     where
     inl : X → PushoutGen Q
     inr : Y → PushoutGen Q
     push : {x : X} {y : Y} → Q x y → inl x ≡ inr y

-- The usual pushout is a special case of the above
module _ {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃}
         (f : A → B) (g : A → C) where
  open Iso

  doubleFib : B → C → Type _
  doubleFib b c = Σ[ a ∈ A ] (f a ≡ b) × (g a ≡ c)

  PushoutGenFib = PushoutGen doubleFib

  Pushout→PushoutGen : Pushout f g → PushoutGenFib
  Pushout→PushoutGen (inl x) = inl x
  Pushout→PushoutGen (inr x) = inr x
  Pushout→PushoutGen (push a i) = push (a , refl , refl) i

  PushoutGen→Pushout : PushoutGenFib → Pushout f g
  PushoutGen→Pushout (inl x) = inl x
  PushoutGen→Pushout (inr x) = inr x
  PushoutGen→Pushout (push (x , p , q) i) =
    ((λ i → inl (p (~ i))) ∙∙ push x ∙∙ (λ i → inr (q i))) i

  IsoPushoutPushoutGen : Iso (Pushout f g) (PushoutGenFib)
  fun IsoPushoutPushoutGen = Pushout→PushoutGen
  inv IsoPushoutPushoutGen = PushoutGen→Pushout
  rightInv IsoPushoutPushoutGen (inl x) = refl
  rightInv IsoPushoutPushoutGen (inr x) = refl
  rightInv IsoPushoutPushoutGen (push (x , p , q) i) j = lem x p q j i
    where
    lem : {b : B} {c : C} (x : A) (p : f x ≡ b) (q : g x ≡ c)
      → cong Pushout→PushoutGen (cong PushoutGen→Pushout (push (x , p , q)))
      ≡ push (x , p , q)
    lem {c = c} x =
      J (λ b p → (q : g x ≡ c)
        → cong Pushout→PushoutGen
           (cong PushoutGen→Pushout (push (x , p , q)))
         ≡ push (x , p , q))
        (J (λ c q → cong Pushout→PushoutGen
                      (cong PushoutGen→Pushout (push (x , refl , q)))
         ≡ push (x , refl , q))
         (cong (cong Pushout→PushoutGen) (sym (rUnit (push x)))))
  leftInv IsoPushoutPushoutGen (inl x) = refl
  leftInv IsoPushoutPushoutGen (inr x) = refl
  leftInv IsoPushoutPushoutGen (push a i) j = rUnit (push a) (~ j) i

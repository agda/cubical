{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.Susp.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Data.Bool
open import Cubical.HITs.Join
open import Cubical.HITs.Susp.Base

Susp-iso-joinBool : ∀ {ℓ} {A : Type ℓ} → Iso (Susp A) (join A Bool)
Iso.fun Susp-iso-joinBool north = inr true
Iso.fun Susp-iso-joinBool south = inr false
Iso.fun Susp-iso-joinBool (merid a i) = (sym (push a true) ∙ push a false) i
Iso.inv Susp-iso-joinBool (inr true ) = north
Iso.inv Susp-iso-joinBool (inr false) = south
Iso.inv Susp-iso-joinBool (inl _) = north
Iso.inv Susp-iso-joinBool (push a true  i) = north
Iso.inv Susp-iso-joinBool (push a false i) = merid a i
Iso.rightInv Susp-iso-joinBool (inr true ) = refl
Iso.rightInv Susp-iso-joinBool (inr false) = refl
Iso.rightInv Susp-iso-joinBool (inl a) = sym (push a true)
Iso.rightInv Susp-iso-joinBool (push a true  i) j = push a true (i ∨ ~ j)
Iso.rightInv Susp-iso-joinBool (push a false i) j
  = hcomp (λ k → λ { (i = i0) → push a true (~ j)
                   ; (i = i1) → push a false k
                   ; (j = i1) → push a false (i ∧ k) })
          (push a true (~ i ∧ ~ j))
Iso.leftInv Susp-iso-joinBool north = refl
Iso.leftInv Susp-iso-joinBool south = refl
Iso.leftInv (Susp-iso-joinBool {A = A}) (merid a i) j
  = hcomp (λ k → λ { (i = i0) → transp (λ _ → Susp A) (k ∨ j) north
                   ; (i = i1) → transp (λ _ → Susp A) (k ∨ j) (merid a k)
                   ; (j = i1) → merid a (i ∧ k) })
          (transp (λ _ → Susp A) j north)

Susp≃joinBool : ∀ {ℓ} {A : Type ℓ} → Susp A ≃ join A Bool
Susp≃joinBool = isoToEquiv Susp-iso-joinBool

Susp≡joinBool : ∀ {ℓ} {A : Type ℓ} → Susp A ≡ join A Bool
Susp≡joinBool = isoToPath Susp-iso-joinBool

congSuspEquiv : ∀ {ℓ} {A B : Type ℓ} → A ≃ B → Susp A ≃ Susp B
congSuspEquiv {ℓ} {A} {B} h = isoToEquiv isom
  where isom : Iso (Susp A) (Susp B)
        Iso.fun isom north = north
        Iso.fun isom south = south
        Iso.fun isom (merid a i) = merid (fst h a) i
        Iso.inv isom north = north
        Iso.inv isom south = south
        Iso.inv isom (merid a i) = merid (invEq h a) i
        Iso.rightInv isom north = refl
        Iso.rightInv isom south = refl
        Iso.rightInv isom (merid a i) j = merid (retEq h a j) i
        Iso.leftInv isom north = refl
        Iso.leftInv isom south = refl
        Iso.leftInv isom (merid a i) j = merid (secEq h a j) i

suspToPropRec : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Susp A → Type ℓ'} (a : A)
                 → ((x : Susp A) → isProp (B x))
                 → B north
                 → (x : Susp A) → B x
suspToPropRec a isProp Bnorth north = Bnorth
suspToPropRec {B = B} a isProp Bnorth south = subst B (merid a) Bnorth
suspToPropRec {B = B} a isProp Bnorth (merid a₁ i) =
  hcomp (λ k → λ {(i = i0) → Bnorth ;
                   (i = i1) → isProp
                                south
                                (subst B (merid a₁) Bnorth)
                                (subst B (merid a) Bnorth) k})
        (transp (λ j → B (merid a₁ (j ∧ i))) (~ i) Bnorth)

suspToPropRec2 : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Susp A → Susp A → Type ℓ'} (a : A)
                 → ((x y : Susp A) → isProp (B x y))
                 → B north north
                 → (x y : Susp A) → B x y
suspToPropRec2 a isProp Bnorth =
  suspToPropRec a (λ x → isOfHLevelΠ 1 λ y → isProp x y)
                      (suspToPropRec a (λ x → isProp north x) Bnorth)

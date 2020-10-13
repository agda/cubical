{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.HITs.Susp.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Data.Bool
open import Cubical.HITs.Join
open import Cubical.HITs.Susp.Base

open Iso

Susp-iso-joinBool : ∀ {ℓ} {A : Type ℓ} → Iso (Susp A) (join A Bool)
fun Susp-iso-joinBool north = inr true
fun Susp-iso-joinBool south = inr false
fun Susp-iso-joinBool (merid a i) = (sym (push a true) ∙ push a false) i
inv Susp-iso-joinBool (inr true ) = north
inv Susp-iso-joinBool (inr false) = south
inv Susp-iso-joinBool (inl _) = north
inv Susp-iso-joinBool (push a true  i) = north
inv Susp-iso-joinBool (push a false i) = merid a i
rightInv Susp-iso-joinBool (inr true ) = refl
rightInv Susp-iso-joinBool (inr false) = refl
rightInv Susp-iso-joinBool (inl a) = sym (push a true)
rightInv Susp-iso-joinBool (push a true  i) j = push a true (i ∨ ~ j)
rightInv Susp-iso-joinBool (push a false i) j
  = hcomp (λ k → λ { (i = i0) → push a true (~ j)
                   ; (i = i1) → push a false k
                   ; (j = i1) → push a false (i ∧ k) })
          (push a true (~ i ∧ ~ j))
leftInv Susp-iso-joinBool north = refl
leftInv Susp-iso-joinBool south = refl
leftInv (Susp-iso-joinBool {A = A}) (merid a i) j
  = hcomp (λ k → λ { (i = i0) → transp (λ _ → Susp A) (k ∨ j) north
                   ; (i = i1) → transp (λ _ → Susp A) (k ∨ j) (merid a k)
                   ; (j = i1) → merid a (i ∧ k) })
          (transp (λ _ → Susp A) j north)

Susp≃joinBool : ∀ {ℓ} {A : Type ℓ} → Susp A ≃ join A Bool
Susp≃joinBool = isoToEquiv (Iso.fun isom) (Iso.inv isom) (Iso.rightInv isom) (Iso.leftInv isom)
  where isom = Susp-iso-joinBool

Susp≡joinBool : ∀ {ℓ} {A : Type ℓ} → Susp A ≡ join A Bool
Susp≡joinBool = isoToPath Susp-iso-joinBool

congSuspEquiv : ∀ {ℓ} {A B : Type ℓ} → A ≃ B → Susp A ≃ Susp B
congSuspEquiv {ℓ} {A} {B} h = isoToEquiv f g fg gf
  where
  f : Susp A → _
  f north = north
  f south = south
  f (merid a i) = merid (fst h a) i
  g : Susp B → _
  g north = north
  g south = south
  g (merid a i) = merid (invEq h a) i
  fg : (b : Susp B) → _
  fg north = refl
  fg south = refl
  fg (merid a i) j = merid (retEq h a j) i
  gf : (a : Susp A) → _
  gf north = refl
  gf south = refl
  gf (merid a i) j = merid (secEq h a j) i

suspToPropRec : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Susp A → Type ℓ'} (a : A)
                 → ((x : Susp A) → isProp (B x))
                 → B north
                 → (x : Susp A) → B x
suspToPropRec a isProp Bnorth north = Bnorth
suspToPropRec {B = B} a isProp Bnorth south = subst B (merid a) Bnorth
suspToPropRec {B = B} a isProp Bnorth (merid a₁ i) =
  isOfHLevel→isOfHLevelDep 1 isProp Bnorth (subst B (merid a) Bnorth) (merid a₁) i

suspToPropRec2 : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Susp A → Susp A → Type ℓ'} (a : A)
                 → ((x y : Susp A) → isProp (B x y))
                 → B north north
                 → (x y : Susp A) → B x y
suspToPropRec2 a isProp Bnorth =
  suspToPropRec a (λ x → isOfHLevelΠ 1 λ y → isProp x y)
                      (suspToPropRec a (λ x → isProp north x) Bnorth)

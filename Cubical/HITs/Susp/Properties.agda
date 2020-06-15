{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.HITs.Susp.Properties where

open import Cubical.Foundations.Prelude
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
Susp≃joinBool = isoToEquiv Susp-iso-joinBool

Susp≡joinBool : ∀ {ℓ} {A : Type ℓ} → Susp A ≡ join A Bool
Susp≡joinBool = isoToPath Susp-iso-joinBool

congSuspEquiv : ∀ {ℓ} {A B : Type ℓ} → A ≃ B → Susp A ≃ Susp B
congSuspEquiv {ℓ} {A} {B} h = isoToEquiv isom
  where isom : Iso (Susp A) (Susp B)
        fun isom north = north
        fun isom south = south
        fun isom (merid a i) = merid (fst h a) i
        inv isom north = north
        inv isom south = south
        inv isom (merid a i) = merid (invEq h a) i
        rightInv isom north = refl
        rightInv isom south = refl
        rightInv isom (merid a i) j = merid (retEq h a j) i
        leftInv isom north = refl
        leftInv isom south = refl
        leftInv isom (merid a i) j = merid (secEq h a j) i

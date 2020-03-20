{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.Susp.Properties where

open import Cubical.Foundations.Prelude
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

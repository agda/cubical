{-

Theory about Bi-Invertible Equivalences

- BiInvEquiv to Iso
- BiInvEquiv to Equiv
- Iso to BiInvEquiv

-}
{-# OPTIONS --cubical --safe #-}
module Cubical.Foundations.BiInvEquiv where

open import Cubical.Core.Glue

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism


record BiInvEquiv {ℓ ℓ'} (A : Type ℓ) (B : Type ℓ') : Type (ℓ-max ℓ ℓ') where
  constructor biInvEquiv
  field
    fun : A → B
    invr : B → A
    invr-rightInv : section fun invr
    invl : B → A
    invl-leftInv : retract fun invl


  invr-filler : ∀ z {w} (p : invl z ≡ w) → I → I → A
  invr-filler z p j i = hfill (λ j → λ { (i = i0) → invl-leftInv (invr z) j
                                       ; (i = i1) → p j })
                              (inS (invl (invr-rightInv z i))) j

  invr≡invl : ∀ z → invr z ≡ invl z
  invr≡invl z i = invr-filler z refl i1 i

  invr-leftInv : retract fun invr
  invr-leftInv z i = invr-filler (fun z) (invl-leftInv z) i1 i


  invl-rightInv : section fun invl
  invl-rightInv = subst (section fun) (funExt invr≡invl) invr-rightInv

  -- (what's the relationship between this proof and invl-rightInv?)
  invl-rightInv' : section fun invl
  invl-rightInv' z i = hcomp (λ j → λ { (i = i0) → fun (invl (invr-rightInv z j))
                                      ; (i = i1) → invr-rightInv z j })
                             (fun (invl-leftInv (invr z) i))


module _ {ℓ} {A B : Type ℓ} (e : BiInvEquiv A B) where
  open BiInvEquiv e

  biInvEquiv→Iso : Iso A B
  Iso.fun biInvEquiv→Iso      = fun
  Iso.inv biInvEquiv→Iso      = invr
  Iso.rightInv biInvEquiv→Iso = invr-rightInv
  Iso.leftInv biInvEquiv→Iso  = invr-leftInv

  biInvEquiv→Equiv : A ≃ B
  biInvEquiv→Equiv = fun , isoToIsEquiv biInvEquiv→Iso


module _ {ℓ} {A B : Type ℓ} (i : Iso A B) where
  open Iso i

  iso→BiInvEquiv : BiInvEquiv A B
  BiInvEquiv.fun iso→BiInvEquiv           = fun
  BiInvEquiv.invr iso→BiInvEquiv          = inv
  BiInvEquiv.invr-rightInv iso→BiInvEquiv = rightInv
  BiInvEquiv.invl iso→BiInvEquiv          = inv
  BiInvEquiv.invl-leftInv iso→BiInvEquiv  = leftInv


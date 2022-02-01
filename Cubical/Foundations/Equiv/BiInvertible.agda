{-

Some theory about Bi-Invertible Equivalences

- BiInvEquiv to Iso
- BiInvEquiv to Equiv
- BiInvEquiv to HAEquiv
- Iso to BiInvEquiv

-}
{-# OPTIONS --safe #-}
module Cubical.Foundations.Equiv.BiInvertible where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint


record BiInvEquiv {ℓ ℓ'} (A : Type ℓ) (B : Type ℓ') : Type (ℓ-max ℓ ℓ') where
  constructor biInvEquiv
  field
    fun : A → B
    invr : B → A
    invr-rightInv : section fun invr
    invl : B → A
    invl-leftInv : retract fun invl

  invr≡invl : ∀ b → invr b ≡ invl b
  invr≡invl b =            invr b   ≡⟨ sym (invl-leftInv (invr b)) ⟩
                invl (fun (invr b)) ≡⟨ cong invl (invr-rightInv b) ⟩
                invl b              ∎

  invr-leftInv : retract fun invr
  invr-leftInv a = invr≡invl (fun a) ∙ (invl-leftInv a)

  invr≡invl-leftInv : ∀ a → PathP (λ j → invr≡invl (fun a) j ≡ a) (invr-leftInv a) (invl-leftInv a)
  invr≡invl-leftInv a j i = compPath-filler' (invr≡invl (fun a)) (invl-leftInv a) (~ j) i

  invl-rightInv : section fun invl
  invl-rightInv a = sym (cong fun (invr≡invl a)) ∙ (invr-rightInv a)

  invr≡invl-rightInv : ∀ a → PathP (λ j → fun (invr≡invl a j) ≡ a) (invr-rightInv a) (invl-rightInv a)
  invr≡invl-rightInv a j i = compPath-filler' (sym (cong fun (invr≡invl a))) (invr-rightInv a) j i


module _ {ℓ} {A B : Type ℓ} (e : BiInvEquiv A B) where
  open BiInvEquiv e

  biInvEquiv→Iso-right : Iso A B
  Iso.fun biInvEquiv→Iso-right      = fun
  Iso.inv biInvEquiv→Iso-right      = invr
  Iso.rightInv biInvEquiv→Iso-right = invr-rightInv
  Iso.leftInv biInvEquiv→Iso-right  = invr-leftInv

  biInvEquiv→Iso-left : Iso A B
  Iso.fun biInvEquiv→Iso-left      = fun
  Iso.inv biInvEquiv→Iso-left      = invl
  Iso.rightInv biInvEquiv→Iso-left = invl-rightInv
  Iso.leftInv biInvEquiv→Iso-left  = invl-leftInv

  biInvEquiv→Equiv-right biInvEquiv→Equiv-left : A ≃ B
  biInvEquiv→Equiv-right = fun , isoToIsEquiv biInvEquiv→Iso-right
  biInvEquiv→Equiv-left  = fun , isoToIsEquiv biInvEquiv→Iso-left

  -- since Iso.rightInv ends up getting modified during iso→HAEquiv, in some sense biInvEquiv→Iso-left
  --  is the most natural choice for forming a HAEquiv from a BiInvEquiv
  biInvEquiv→HAEquiv : HAEquiv A B
  biInvEquiv→HAEquiv = iso→HAEquiv biInvEquiv→Iso-left


module _ {ℓ} {A B : Type ℓ} (i : Iso A B) where
  open Iso i

  iso→BiInvEquiv : BiInvEquiv A B
  BiInvEquiv.fun iso→BiInvEquiv           = fun
  BiInvEquiv.invr iso→BiInvEquiv          = inv
  BiInvEquiv.invr-rightInv iso→BiInvEquiv = rightInv
  BiInvEquiv.invl iso→BiInvEquiv          = inv
  BiInvEquiv.invl-leftInv iso→BiInvEquiv  = leftInv


{-# OPTIONS --safe #-}

module Cubical.Functions.Involution where

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence

isInvolution : ∀{ℓ} {A : Type ℓ} → (A → A) → Type _
isInvolution f = ∀ x → f (f x) ≡ x

module _ {ℓ} {A : Type ℓ} {f : A → A} (invol : isInvolution f) where
  open Iso

  involIso : Iso A A
  involIso .fun = f
  involIso .inv = f
  involIso .rightInv = invol
  involIso .leftInv = invol

  involIsEquiv : isEquiv f
  involIsEquiv = isoToIsEquiv involIso

  involEquiv : A ≃ A
  involEquiv = f , involIsEquiv

  involPath : A ≡ A
  involPath = ua involEquiv

  involEquivComp : compEquiv involEquiv involEquiv ≡ idEquiv A
  involEquivComp
    = equivEq (λ i x → invol x i)

  involPathComp : involPath ∙ involPath ≡ refl
  involPathComp
    = sym (uaCompEquiv involEquiv involEquiv) ∙∙ cong ua involEquivComp ∙∙ uaIdEquiv

  involPath² : Square involPath refl refl involPath
  involPath²
    = subst (λ s → Square involPath s refl involPath)
        involPathComp (compPath-filler involPath involPath)

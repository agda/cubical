{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.Localistation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Logic
open import Cubical.Foundations.Transport
open import Cubical.Functions.FunExtEquiv

import Cubical.Data.Empty as ⊥
open import Cubical.Data.Bool
open import Cubical.Data.Nat hiding (_+_ ; +-comm ; +-assoc)
open import Cubical.Data.Vec
open import Cubical.Data.Sigma.Base
open import Cubical.Data.FinData
open import Cubical.Relation.Nullary

open import Cubical.Structures.Group hiding (⟨_⟩)
open import Cubical.Structures.AbGroup hiding (⟨_⟩)
open import Cubical.Structures.Monoid hiding (⟨_⟩)
open import Cubical.Structures.Ring hiding (⟨_⟩)
open import Cubical.Structures.CommRing

open Iso

private
  variable
    ℓ : Level
    A : Type ℓ

record isSubMonoid (RX : CommRing {ℓ}) (S : ℙ ⟨ RX ⟩) : Type ℓ where
 constructor
   submonoid
 field
   containsOne : (RX .CommRing.1r) ∈ S
   multClosed : ∀ s t → s ∈ S → t ∈ S → (RX .CommRing._·_ s t) ∈ S

module _(RX : CommRing {ℓ}) (S : ℙ ⟨ RX ⟩) (SsubMonoid : isSubMonoid RX S) where
 open CommRing

 R = ⟨ RX ⟩
 0ᴿ = RX .0r
 1ᴿ = RX .1r
 _+ᴿ_ = RX ._+_
 _·ᴿ_ = RX ._·_
 -ᴿ_ = RX .-_
 _-ᴿ_ : R → R → R
 _-ᴿ_ = λ x y → x +ᴿ (-ᴿ y)

 data S⁻¹R : Type ℓ where
  _/_ : (r s : R) → {s ∈ S} → S⁻¹R
  zd : {r₁ r₂ s s₁ s₂ : R} → {s ∈ S} → {a : s₁ ∈ S} → {b : s₂ ∈ S}
     → s ·ᴿ ((r₁ ·ᴿ s₂) -ᴿ (r₂ ·ᴿ s₁)) ≡ 0ᴿ
     → ((r₁ / s₁) {a}) ≡ ((r₂ / s₂) {b})

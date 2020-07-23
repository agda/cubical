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
    ℓ ℓ' : Level
    A : Type ℓ

record isSubMonoid (RX : CommRing {ℓ}) (S : ℙ ⟨ RX ⟩) : Type ℓ where
 constructor
   submonoid
 field
   containsOne : (RX .CommRing.1r) ∈ S
   multClosed : ∀ s t → s ∈ S → t ∈ S → (RX .CommRing._·_ s t) ∈ S

module _(RX : CommRing {ℓ}) (S : ℙ ⟨ RX ⟩) (SsubMonoid : isSubMonoid RX S) where
 open isSubMonoid
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
  zd : (r₁ r₂ s s₁ s₂ : R) → {s ∈ S} → {a : s₁ ∈ S} → {b : s₂ ∈ S}
     → s ·ᴿ ((r₁ ·ᴿ s₂) -ᴿ (r₂ ·ᴿ s₁)) ≡ 0ᴿ
     → ((r₁ / s₁) {a}) ≡ ((r₂ / s₂) {b})
  trunc : isSet S⁻¹R

 infixr 15 _/_

 module Elim {ℓ'} {B : S⁻¹R → Type ℓ'}
     (_/*_ : (r s : R) → {a : s ∈ S} → B ((r / s) {a}))
     (zd* : (r₁ r₂ s s₁ s₂ : R) → {c : s ∈ S} → {a : s₁ ∈ S} → {b : s₂ ∈ S}
          → (p : s ·ᴿ ((r₁ ·ᴿ s₂) -ᴿ (r₂ ·ᴿ s₁)) ≡ 0ᴿ)
          → PathP (λ i → B (zd r₁ r₂ s s₁ s₂ {c} {a} {b} p i))  ((r₁ /* s₁) {a}) ((r₂ /* s₂) {b}))
     (trunc* : (q : S⁻¹R) → isSet (B q)) where


  f : (q : S⁻¹R) → B q
  f (r / s) = r /* s
  f (zd r₁ r₂ s s₁ s₂ p i) = zd* r₁ r₂ s s₁ s₂ p i
  f (trunc q₁ q₂ x y i j) = isOfHLevel→isOfHLevelDep 2 trunc*  (f q₁) (f q₂) (cong f x) (cong f y)
                                                      (trunc q₁ q₂ x y) i j


 module ElimProp {ℓ'} {B : S⁻¹R → Type ℓ'} (Bprop : {q : S⁻¹R} → isProp (B q))
                 (_/*_ : (r s : R) → {a : s ∈ S} → B ((r / s) {a})) where


  f : (q : S⁻¹R) → B q
  f = Elim.f _/*_ (λ r₁ r₂ s s₁ s₂ {c} {a} {b} p
    → toPathP (Bprop (transp (λ i → B (zd r₁ r₂ s s₁ s₂ {c} {a} {b} p i)) i0 (r₁ /* s₁))
              (r₂ /* s₂)))
             λ q → isProp→isSet Bprop


 module Rec {ℓ'} {B : Type ℓ'} (BType : isSet B)
     (_/*_ : (r s : R) → {s ∈ S} → B)
     (zd* : (r₁ r₂ s s₁ s₂ : R) → {c : s ∈ S} → {a : s₁ ∈ S} → {b : s₂ ∈ S}
          → (p : s ·ᴿ ((r₁ ·ᴿ s₂) -ᴿ (r₂ ·ᴿ s₁)) ≡ 0ᴿ)
          → ((r₁ /* s₁) {a}) ≡ ((r₂ /* s₂) {b}))
     where

  f : S⁻¹R → B
  f = Elim.f _/*_ zd* (λ _ → BType)


 _+ₗ_ : S⁻¹R → S⁻¹R → S⁻¹R
 _+ₗ_ = Rec.f {!!} {!!} {!!}
  where
  α : R → (s : R) {a : s ∈ S} → S⁻¹R → S⁻¹R
  α r s {a} = Rec.f trunc (λ r' s' {b} → ((r ·ᴿ s') +ᴿ (r' ·ᴿ s) / s ·ᴿ s')
                          {SsubMonoid .multClosed s s' a b})
                          {!!}
   where

    --                 λ r₁ r₂ s₃ s₁ s₂ {c} {a} {b} p i → zd ((r ·ᴿ s₁) +ᴿ (r₁ ·ᴿ s))
    --                                                       ((r ·ᴿ s₂) +ᴿ (r₂ ·ᴿ s))
    --                                                       _ _ _ {c} {a} {b} {!!} {!!}
    -- where
    -- path : ((r ·ᴿ s₁) +ᴿ (r₁ ·ᴿ s)) ·ᴿ s₂ ≡ ((r ·ᴿ s₂) +ᴿ (r₂ ·ᴿ s)) ·ᴿ s₁
    -- path = ?

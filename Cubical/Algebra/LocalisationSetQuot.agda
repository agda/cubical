{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.LocalisationSetQuot where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Logic hiding ([_])
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

open import Cubical.HITs.SetQuotients as SQ
open import Cubical.HITs.PropositionalTruncation as PT

open Iso

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ

record isSubMonoid (R' : CommRing {ℓ}) (S' : ℙ ⟨ R' ⟩) : Type ℓ where
 constructor
   submonoid
 field
   containsOne : (R' .CommRing.1r) ∈ S'
   multClosed : ∀ {s t} → s ∈ S' → t ∈ S' → (R' .CommRing._·_ s t) ∈ S'

module _(R' : CommRing {ℓ}) (S' : ℙ ⟨ R' ⟩) (SsubMonoid : isSubMonoid R' S') where
 open isSubMonoid
 open CommRing R' renaming (Carrier to R)
 open Theory (CommRing→Ring R')

 S = Σ[ s ∈ R ] (s ∈ S')

 -- adapted HIT definition
 data S⁻¹R : Type ℓ where
  _/l_ : R → S → S⁻¹R
  zd : (r₁ r₂ : R) (s s₁ s₂ : S)
     → fst s · r₁ · fst s₂ ≡ fst s · r₂ · fst s₁
     → r₁ /l s₁ ≡ r₂ /l s₂
  trunc : isSet S⁻¹R

 infixr 5 _/l_


 module Elim {ℓ'} {B : S⁻¹R → Type ℓ'}
     (_/*_ : (r : R) (s : S) → B (r /l s))
     (zd* : (r₁ r₂ : R) (s s₁ s₂  : S)
          → (p : fst s · r₁ · fst s₂ ≡ fst s · r₂ · fst s₁)
          → PathP (λ i → B (zd r₁ r₂ s s₁ s₂ p i))  (r₁ /* s₁) (r₂ /* s₂))
     (trunc* : (q : S⁻¹R) → isSet (B q)) where


  f : (q : S⁻¹R) → B q
  f (r /l s) = r /* s
  f (zd r₁ r₂ s s₁ s₂ p i) = zd* r₁ r₂ s s₁ s₂ p i
  f (trunc q₁ q₂ x y i j) = isOfHLevel→isOfHLevelDep 2 trunc*  (f q₁) (f q₂) (cong f x) (cong f y)
                                                      (trunc q₁ q₂ x y) i j


 module ElimProp {ℓ'} {B : S⁻¹R → Type ℓ'} (Bprop : {q : S⁻¹R} → isProp (B q))
                 (_/*_ : (r : R) → (s : S) → B (r /l s)) where


  f : (q : S⁻¹R) → B q
  f = Elim.f _/*_ (λ r₁ r₂ s s₁ s₂ p
    → toPathP (Bprop (transp (λ i → B (zd r₁ r₂ s s₁ s₂ p i)) i0 (r₁ /* s₁))
              (r₂ /* s₂)))
             λ q → isProp→isSet Bprop


 module Rec {ℓ'} {B : Type ℓ'} (BType : isSet B)
     (_/*_ : R → S → B)
     (zd* : (r₁ r₂ : R) (s s₁ s₂ : S)
          → (p : fst s · r₁ · fst s₂ ≡ fst s · r₂ · fst s₁)
          → r₁ /* s₁ ≡ r₂ /* s₂)
     where

  f : S⁻¹R → B
  f = Elim.f _/*_ zd* (λ _ → BType)


 -- approach using set quotients
 _≈_ : R × S → R × S → Type ℓ
 (r₁ , s₁) ≈ (r₂ , s₂) = ∃[ s ∈ S ] (fst s · r₁ · fst s₂ ≡ fst s · r₂ · fst s₁)

 S⁻¹R/ = (R × S) / _≈_

 -- proving equivalence of the two types
 φ : S⁻¹R/ → S⁻¹R
 φ = SQ.rec trunc (λ (r , s) → r /l s) β
  where
  α : ((r₁ , s₁) (r₂ , s₂) : R × S) → Σ[ s ∈ S ] (fst s · r₁ · fst s₂ ≡ fst s · r₂ · fst s₁)
    → r₁ /l s₁ ≡ r₂ /l s₂
  α _ _ (s , p) = zd _ _ s _ _ p

  β : ((r₁ , s₁) (r₂ , s₂) : R × S) → ∃[ s ∈ S ] (fst s · r₁ · fst s₂ ≡ fst s · r₂ · fst s₁)
    → r₁ /l s₁ ≡ r₂ /l s₂
  β _ _ = PT.rec (trunc _ _) (α _ _)

 ψ : S⁻¹R → S⁻¹R/
 ψ (r /l s) = [ r , s ]
 ψ (zd r₁ r₂ s s₁ s₂ p i) = eq/ (r₁ , s₁) (r₂ , s₂) ∣ s , p ∣ i
 ψ (trunc x y p q i j) = squash/ (ψ x) (ψ y) (cong ψ p) (cong ψ q) i j

 η : section φ ψ
 η = ElimProp.f (trunc _ _) λ _ _ → refl

 ε : retract φ ψ
 ε = elimProp (λ _ → squash/ _ _) λ _ → refl

 S⁻¹R/≃S⁻¹R : S⁻¹R/ ≃ S⁻¹R
 S⁻¹R/≃S⁻¹R = isoToEquiv (iso φ ψ η ε)

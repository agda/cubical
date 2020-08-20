{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.LocalisationSetQuot where

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

open import Cubical.HITs.SetQuotients
open import Cubical.HITs.PropositionalTruncation

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

 -- approach using set quotients
 _≈_ : R × S → R × S → Type ℓ
 (r₁ , s₁) ≈ (r₂ , s₂) = ∃[ s ∈ S ] (fst s · r₁ · fst s₂ ≡ fst s · r₂ · fst s₁)

 S⁻¹R/ = (R × S) / _≈_

 φ : S⁻¹R/ → S⁻¹R
 φ = Cubical.HITs.SetQuotients.rec trunc (λ (r , s) → r /l s) β
  where
  α : ((r₁ , s₁) (r₂ , s₂) : R × S) → Σ[ s ∈ S ] (fst s · r₁ · fst s₂ ≡ fst s · r₂ · fst s₁)
    → r₁ /l s₁ ≡ r₂ /l s₂
  α (r₁ , s₁) (r₂ , s₂) (s , p) = zd _ _ s s₁ s₂ p

  β : ((r₁ , s₁) (r₂ , s₂) : R × S) → ∃[ s ∈ S ] (fst s · r₁ · fst s₂ ≡ fst s · r₂ · fst s₁)
    → r₁ /l s₁ ≡ r₂ /l s₂
  β (r₁ , s₁) (r₂ , s₂) r = elim→Set (λ _ → isProp→isSet (trunc _ _)) (α (r₁ , s₁) (r₂ , s₂))
              (λ (s , p) (s' , p') j → trunc _ _ (zd _ _ s s₁ s₂ p) (zd _ _ s' s₁ s₂ p') j) r


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
open import Cubical.Data.Sigma.Properties
open import Cubical.Data.FinData
open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary

open import Cubical.Algebra.Group hiding (⟨_⟩)
open import Cubical.Algebra.AbGroup hiding (⟨_⟩)
open import Cubical.Algebra.Monoid hiding (⟨_⟩)
open import Cubical.Algebra.Ring hiding (⟨_⟩)
open import Cubical.Algebra.CommRing

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
  _/ₗ_ : R → S → S⁻¹R
  zd : (r₁ r₂ : R) (s s₁ s₂ : S)
     → fst s · r₁ · fst s₂ ≡ fst s · r₂ · fst s₁
     → r₁ /ₗ s₁ ≡ r₂ /ₗ s₂
  trunc : isSet S⁻¹R

 infixr 5 _/ₗ_


 module Elim {ℓ'} {B : S⁻¹R → Type ℓ'}
     (_/*_ : (r : R) (s : S) → B (r /ₗ s))
     (zd* : (r₁ r₂ : R) (s s₁ s₂  : S)
          → (p : fst s · r₁ · fst s₂ ≡ fst s · r₂ · fst s₁)
          → PathP (λ i → B (zd r₁ r₂ s s₁ s₂ p i))  (r₁ /* s₁) (r₂ /* s₂))
     (trunc* : (q : S⁻¹R) → isSet (B q)) where


  f : (q : S⁻¹R) → B q
  f (r /ₗ s) = r /* s
  f (zd r₁ r₂ s s₁ s₂ p i) = zd* r₁ r₂ s s₁ s₂ p i
  f (trunc q₁ q₂ x y i j) = isOfHLevel→isOfHLevelDep 2 trunc*  (f q₁) (f q₂) (cong f x) (cong f y)
                                                      (trunc q₁ q₂ x y) i j


 module ElimProp {ℓ'} {B : S⁻¹R → Type ℓ'} (Bprop : {q : S⁻¹R} → isProp (B q))
                 (_/*_ : (r : R) → (s : S) → B (r /ₗ s)) where


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
 φ = SQ.rec trunc (λ (r , s) → r /ₗ s) β
  where
  α : ((r₁ , s₁) (r₂ , s₂) : R × S) → Σ[ s ∈ S ] (fst s · r₁ · fst s₂ ≡ fst s · r₂ · fst s₁)
    → r₁ /ₗ s₁ ≡ r₂ /ₗ s₂
  α _ _ (s , p) = zd _ _ s _ _ p

  β : ((r₁ , s₁) (r₂ , s₂) : R × S) → ∃[ s ∈ S ] (fst s · r₁ · fst s₂ ≡ fst s · r₂ · fst s₁)
    → r₁ /ₗ s₁ ≡ r₂ /ₗ s₂
  β _ _ = PT.rec (trunc _ _) (α _ _)

 ψ : S⁻¹R → S⁻¹R/
 ψ (r /ₗ s) = [ r , s ]
 ψ (zd r₁ r₂ s s₁ s₂ p i) = eq/ (r₁ , s₁) (r₂ , s₂) ∣ s , p ∣ i
 ψ (trunc x y p q i j) = squash/ (ψ x) (ψ y) (cong ψ p) (cong ψ q) i j

 η : section φ ψ
 η = ElimProp.f (trunc _ _) λ _ _ → refl

 ε : retract φ ψ
 ε = elimProp (λ _ → squash/ _ _) λ _ → refl

 S⁻¹R/≃S⁻¹R : S⁻¹R/ ≃ S⁻¹R
 S⁻¹R/≃S⁻¹R = isoToEquiv (iso φ ψ η ε)


 -- try to develop theory with set-quotients, for this
 -- define a third type:
 _≈'_ : R × S → R × S → Type ℓ
 (r₁ , s₁) ≈' (r₂ , s₂) = Σ[ s ∈ S ] (fst s · r₁ · fst s₂ ≡ fst s · r₂ · fst s₁)

 Rₛ = (R × S) / _≈'_

 Rₛ≃S⁻¹R/ : Rₛ ≃ S⁻¹R/
 Rₛ≃S⁻¹R/ = SQ.truncRelEquiv

 -- now define operations for Rₛ
 open BinaryRelation

 locRefl : isRefl _≈'_
 locRefl _ = (1r , SsubMonoid .containsOne) , refl

 -- quite tedious as well
 -- locTrans : isTrans _≈'_
 -- locTrans = {!!}

 _+ₗ_ : Rₛ → Rₛ → Rₛ
 _+ₗ_ = setQuotBinOp locRefl _+ₚ_ θ
  where
  _+ₚ_ : R × S → R × S → R × S
  (r₁ , s₁ , s₁∈S) +ₚ (r₂ , s₂ , s₂∈S) =
                      (r₁ · s₂ + r₂ · s₁) , (s₁ · s₂) , SsubMonoid .multClosed s₁∈S s₂∈S

  θ : (a a' b b' : R × S) → a ≈' a' → b ≈' b' → (a +ₚ b) ≈' (a' +ₚ b')
  θ (r₁ , s₁ , s₁∈S) (r'₁ , s'₁ , s'₁∈S) (r₂ , s₂ , s₂∈S) (r'₂ , s'₂ , s'₂∈S) (s , p) (s' , q) =
    ((fst s · fst s') , SsubMonoid .multClosed (s .snd) (s' .snd)) , path
    where
    path : fst s · fst s' · (r₁ · s₂ + r₂ · s₁) · (s'₁ · s'₂)
         ≡ fst s · fst s' · (r'₁ · s'₂ + r'₂ · s'₁) · (s₁ · s₂)
    path = fst s · fst s' · (r₁ · s₂ + r₂ · s₁) · (s'₁ · s'₂)
         ≡⟨ cong (_· (s'₁ · s'₂)) (·-rdist-+ _ _ _) ⟩
           (fst s · fst s' · (r₁ · s₂) + fst s · fst s' · (r₂ · s₁)) · (s'₁ · s'₂)
         ≡⟨ ·-ldist-+ _ _ _ ⟩
           fst s · fst s' · (r₁ · s₂) · (s'₁ · s'₂) + fst s · fst s' · (r₂ · s₁) · (s'₁ · s'₂)
         ≡⟨ (λ i → ·-assoc (fst s · fst s') r₁ s₂ i · (s'₁ · s'₂)
                 + ·-assoc (fst s · fst s') r₂ s₁ i · (s'₁ · s'₂)) ⟩
           fst s · fst s' · r₁ · s₂ · (s'₁ · s'₂) + fst s · fst s' · r₂ · s₁ · (s'₁ · s'₂)
         ≡⟨ (λ i → ·-comm (fst s) (fst s') i
                   · r₁ · s₂ · (s'₁ · s'₂) + fst s · fst s' · r₂ · s₁ · (s'₁ · s'₂)) ⟩
           fst s' · fst s · r₁ · s₂ · (s'₁ · s'₂) + fst s · fst s' · r₂ · s₁ · (s'₁ · s'₂)
         ≡⟨ (λ i → ·-assoc (fst s') (fst s) r₁ (~ i)
                   · s₂ · (s'₁ · s'₂) + fst s · fst s' · r₂ · s₁ · (s'₁ · s'₂)) ⟩
           fst s' · (fst s · r₁) · s₂ · (s'₁ · s'₂) + fst s · fst s' · r₂ · s₁ · (s'₁ · s'₂)
         ≡⟨ (λ i → ·-assoc (fst s' · (fst s · r₁) · s₂) s'₁ s'₂ i
                   + fst s · fst s' · r₂ · s₁ · (s'₁ · s'₂)) ⟩
           fst s' · (fst s · r₁) · s₂ · s'₁ · s'₂ + fst s · fst s' · r₂ · s₁ · (s'₁ · s'₂)
         ≡⟨ (λ i → ·-assoc (fst s' · (fst s · r₁)) s₂ s'₁ (~ i)
                   · s'₂ + fst s · fst s' · r₂ · s₁ · (s'₁ · s'₂)) ⟩
           fst s' · (fst s · r₁) · (s₂ · s'₁) · s'₂ + fst s · fst s' · r₂ · s₁ · (s'₁ · s'₂)
         ≡⟨ (λ i → fst s' · (fst s · r₁) · (·-comm s₂ s'₁ i) · s'₂
                   + fst s · fst s' · r₂ · s₁ · (s'₁ · s'₂)) ⟩
           fst s' · (fst s · r₁) · (s'₁ · s₂) · s'₂ + fst s · fst s' · r₂ · s₁ · (s'₁ · s'₂)
         ≡⟨ (λ i → ·-assoc (fst s' · (fst s · r₁)) s'₁ s₂ i
                   · s'₂ + fst s · fst s' · r₂ · s₁ · (s'₁ · s'₂)) ⟩
           fst s' · (fst s · r₁) · s'₁ · s₂ · s'₂ + fst s · fst s' · r₂ · s₁ · (s'₁ · s'₂)
         ≡⟨ (λ i → ·-assoc (fst s') (fst s · r₁) s'₁ (~ i)
                   · s₂ · s'₂ + fst s · fst s' · r₂ · s₁ · (s'₁ · s'₂)) ⟩
           fst s' · (fst s · r₁ · s'₁) · s₂ · s'₂ + fst s · fst s' · r₂ · s₁ · (s'₁ · s'₂)
         ≡⟨ (λ i → fst s' · (p i) · s₂ · s'₂ + fst s · fst s' · r₂ · s₁ · (s'₁ · s'₂)) ⟩
           fst s' · (fst s · r'₁ · s₁) · s₂ · s'₂ + fst s · fst s' · r₂ · s₁ · (s'₁ · s'₂)
         ≡⟨ (λ i → ·-assoc (fst s' · (fst s · r'₁ · s₁)) s₂ s'₂ (~ i)
                   + fst s · fst s' · r₂ · s₁ · (s'₁ · s'₂)) ⟩
           fst s' · (fst s · r'₁ · s₁) · (s₂ · s'₂) + fst s · fst s' · r₂ · s₁ · (s'₁ · s'₂)
         ≡⟨ (λ i → fst s' · (fst s · r'₁ · s₁) · (·-comm s₂ s'₂ i)
                   + fst s · fst s' · r₂ · s₁ · (s'₁ · s'₂)) ⟩
           fst s' · (fst s · r'₁ · s₁) · (s'₂ · s₂) + fst s · fst s' · r₂ · s₁ · (s'₁ · s'₂)
         ≡⟨ (λ i → fst s' · (fst s · r'₁ · s₁) · (s'₂ · s₂)
                   + fst s · fst s' · r₂ · s₁ · ·-comm s'₁ s'₂ i) ⟩
           fst s' · (fst s · r'₁ · s₁) · (s'₂ · s₂) + fst s · fst s' · r₂ · s₁ · (s'₂ · s'₁)
         ≡⟨ (λ i → fst s' · (fst s · r'₁ · s₁) · (s'₂ · s₂)
                   + ·-assoc (fst s) (fst s') r₂ (~ i) · s₁ · (s'₂ · s'₁)) ⟩
           fst s' · (fst s · r'₁ · s₁) · (s'₂ · s₂) + fst s · (fst s' · r₂) · s₁ · (s'₂ · s'₁)
         ≡⟨ (λ i → fst s' · (fst s · r'₁ · s₁) · (s'₂ · s₂)
                   + ·-assoc (fst s · (fst s' · r₂) · s₁) s'₂ s'₁ i) ⟩
           fst s' · (fst s · r'₁ · s₁) · (s'₂ · s₂) + fst s · (fst s' · r₂) · s₁ · s'₂ · s'₁
         ≡⟨ (λ i → fst s' · (fst s · r'₁ · s₁) · (s'₂ · s₂)
                   + ·-assoc (fst s · (fst s' · r₂)) s₁ s'₂ (~ i) · s'₁) ⟩
           fst s' · (fst s · r'₁ · s₁) · (s'₂ · s₂) + fst s · (fst s' · r₂) · (s₁ · s'₂) · s'₁
         ≡⟨ (λ i → fst s' · (fst s · r'₁ · s₁) · (s'₂ · s₂)
                   + fst s · (fst s' · r₂) · (·-comm s₁ s'₂ i) · s'₁) ⟩
           fst s' · (fst s · r'₁ · s₁) · (s'₂ · s₂) + fst s · (fst s' · r₂) · (s'₂ · s₁) · s'₁
         ≡⟨ (λ i → fst s' · (fst s · r'₁ · s₁) · (s'₂ · s₂)
                   + ·-assoc (fst s · (fst s' · r₂)) s'₂ s₁ i · s'₁) ⟩
           fst s' · (fst s · r'₁ · s₁) · (s'₂ · s₂) + fst s · (fst s' · r₂) · s'₂ · s₁ · s'₁
         ≡⟨ (λ i → fst s' · (fst s · r'₁ · s₁) · (s'₂ · s₂)
                  + ·-assoc (fst s) (fst s' · r₂) s'₂ (~ i) · s₁ · s'₁) ⟩
           fst s' · (fst s · r'₁ · s₁) · (s'₂ · s₂) + fst s · (fst s' · r₂ · s'₂) · s₁ · s'₁
         ≡⟨ (λ i → fst s' · (fst s · r'₁ · s₁) · (s'₂ · s₂)
                   + ·-assoc (fst s · (fst s' · r₂ · s'₂)) s₁ s'₁ (~ i)) ⟩
           fst s' · (fst s · r'₁ · s₁) · (s'₂ · s₂) + fst s · (fst s' · r₂ · s'₂) · (s₁ · s'₁)
         ≡⟨ (λ i → fst s' · (fst s · r'₁ · s₁) · (s'₂ · s₂)
                   + fst s · (q i) · (·-comm s₁ s'₁ i)) ⟩
           fst s' · (fst s · r'₁ · s₁) · (s'₂ · s₂) + fst s · (fst s' · r'₂ · s₂) · (s'₁ · s₁)
         ≡⟨ (λ i → fst s' · (fst s · r'₁ · s₁) · (s'₂ · s₂)
                   + ·-assoc (fst s · (fst s' · r'₂ · s₂)) s'₁ s₁ i) ⟩
           fst s' · (fst s · r'₁ · s₁) · (s'₂ · s₂) + fst s · (fst s' · r'₂ · s₂) · s'₁ · s₁
         ≡⟨ (λ i → fst s' · (fst s · r'₁ · s₁) · (s'₂ · s₂)
                   + ·-assoc (fst s) (fst s' · r'₂) s₂ i · s'₁ · s₁) ⟩
           fst s' · (fst s · r'₁ · s₁) · (s'₂ · s₂) + fst s · (fst s' · r'₂) · s₂ · s'₁ · s₁
         ≡⟨ (λ i → fst s' · (fst s · r'₁ · s₁) · (s'₂ · s₂)
                   + ·-assoc (fst s · (fst s' · r'₂)) s₂ s'₁ (~ i) · s₁) ⟩
           fst s' · (fst s · r'₁ · s₁) · (s'₂ · s₂) + fst s · (fst s' · r'₂) · (s₂ · s'₁) · s₁
         ≡⟨ (λ i → fst s' · (fst s · r'₁ · s₁) · (s'₂ · s₂)
                   + fst s · (fst s' · r'₂) · (·-comm s₂ s'₁ i) · s₁) ⟩
           fst s' · (fst s · r'₁ · s₁) · (s'₂ · s₂) + fst s · (fst s' · r'₂) · (s'₁ · s₂) · s₁
         ≡⟨ (λ i → fst s' · (fst s · r'₁ · s₁) · (s'₂ · s₂)
                   + ·-assoc (fst s · (fst s' · r'₂)) s'₁ s₂ i · s₁) ⟩
           fst s' · (fst s · r'₁ · s₁) · (s'₂ · s₂) + fst s · (fst s' · r'₂) · s'₁ · s₂ · s₁
         ≡⟨ (λ i → fst s' · (fst s · r'₁ · s₁) · (s'₂ · s₂)
                   + ·-assoc (fst s · (fst s' · r'₂) · s'₁) s₂ s₁ (~ i)) ⟩
           fst s' · (fst s · r'₁ · s₁) · (s'₂ · s₂) + fst s · (fst s' · r'₂) · s'₁ · (s₂ · s₁)
         ≡⟨ (λ i → fst s' · (fst s · r'₁ · s₁) · (s'₂ · s₂)
                   + ·-assoc (fst s) (fst s') r'₂ i · s'₁ · (s₂ · s₁)) ⟩
           fst s' · (fst s · r'₁ · s₁) · (s'₂ · s₂) + fst s · fst s' · r'₂ · s'₁ · (s₂ · s₁)
         ≡⟨ (λ i → fst s' · (fst s · r'₁ · s₁) · (s'₂ · s₂)
                   + fst s · fst s' · r'₂ · s'₁ · ·-comm s₂ s₁ i) ⟩
           fst s' · (fst s · r'₁ · s₁) · (s'₂ · s₂) + fst s · fst s' · r'₂ · s'₁ · (s₁ · s₂)
         ≡⟨ (λ i → ·-assoc (fst s' · (fst s · r'₁ · s₁)) s'₂ s₂ i
                   + fst s · fst s' · r'₂ · s'₁ · (s₁ · s₂)) ⟩
           fst s' · (fst s · r'₁ · s₁) · s'₂ · s₂ + fst s · fst s' · r'₂ · s'₁ · (s₁ · s₂)
         ≡⟨ (λ i → ·-assoc (fst s') (fst s · r'₁) s₁ i
                   · s'₂ · s₂ + fst s · fst s' · r'₂ · s'₁ · (s₁ · s₂)) ⟩
           fst s' · (fst s · r'₁) · s₁ · s'₂ · s₂ + fst s · fst s' · r'₂ · s'₁ · (s₁ · s₂)
         ≡⟨ (λ i → ·-assoc (fst s' · (fst s · r'₁)) s₁ s'₂ (~ i)
                   · s₂ + fst s · fst s' · r'₂ · s'₁ · (s₁ · s₂)) ⟩
           fst s' · (fst s · r'₁) · (s₁ · s'₂) · s₂ + fst s · fst s' · r'₂ · s'₁ · (s₁ · s₂)
         ≡⟨ (λ i → fst s' · (fst s · r'₁) · (·-comm s₁ s'₂ i) · s₂
                   + fst s · fst s' · r'₂ · s'₁ · (s₁ · s₂)) ⟩
           fst s' · (fst s · r'₁) · (s'₂ · s₁) · s₂ + fst s · fst s' · r'₂ · s'₁ · (s₁ · s₂)
         ≡⟨ (λ i → ·-assoc (fst s' · (fst s · r'₁)) s'₂ s₁ i
                   · s₂ + fst s · fst s' · r'₂ · s'₁ · (s₁ · s₂)) ⟩
           fst s' · (fst s · r'₁) · s'₂ · s₁ · s₂ + fst s · fst s' · r'₂ · s'₁ · (s₁ · s₂)
         ≡⟨ (λ i → ·-assoc (fst s' · (fst s · r'₁) · s'₂) s₁ s₂ (~ i)
                   + fst s · fst s' · r'₂ · s'₁ · (s₁ · s₂)) ⟩
           fst s' · (fst s · r'₁) · s'₂ · (s₁ · s₂) + fst s · fst s' · r'₂ · s'₁ · (s₁ · s₂)
         ≡⟨ (λ i → ·-assoc (fst s') (fst s) r'₁ i
                   · s'₂ · (s₁ · s₂) + fst s · fst s' · r'₂ · s'₁ · (s₁ · s₂)) ⟩
           fst s' · fst s · r'₁ · s'₂ · (s₁ · s₂) + fst s · fst s' · r'₂ · s'₁ · (s₁ · s₂)
         ≡⟨ (λ i → ·-comm (fst s') (fst s) i
                   · r'₁ · s'₂ · (s₁ · s₂) + fst s · fst s' · r'₂ · s'₁ · (s₁ · s₂)) ⟩
           fst s · fst s' · r'₁ · s'₂ · (s₁ · s₂) + fst s · fst s' · r'₂ · s'₁ · (s₁ · s₂)
         ≡⟨ (λ i → ·-assoc (fst s · fst s') r'₁ s'₂ (~ i) · (s₁ · s₂)
                 + ·-assoc (fst s · fst s') r'₂ s'₁ (~ i) · (s₁ · s₂)) ⟩
           fst s · fst s' · (r'₁ · s'₂) · (s₁ · s₂) + fst s · fst s' · (r'₂ · s'₁) · (s₁ · s₂)
         ≡⟨ sym (·-ldist-+ _ _ _) ⟩
           (fst s · fst s' · (r'₁ · s'₂)  + fst s · fst s' · (r'₂ · s'₁)) · (s₁ · s₂)
         ≡⟨ cong (_· (s₁ · s₂)) (sym (·-rdist-+ _ _ _)) ⟩
           fst s · fst s' · (r'₁ · s'₂ + r'₂ · s'₁) · (s₁ · s₂) ∎


 -- check group-laws for addition
 0ₗ : Rₛ
 0ₗ = [ 0r , 1r , SsubMonoid .containsOne ]

 +ₗ-rid : (x : Rₛ) → x +ₗ 0ₗ ≡ x
 +ₗ-rid = SQ.elimProp (λ _ → squash/ _ _) +ₗ-rid[]
  where
  +ₗ-rid[] : (a : R × S) → [ a ] +ₗ 0ₗ ≡ [ a ]
  +ₗ-rid[] (r , s , s∈S) = path
   where
   eq1 : r · 1r + 0r · s ≡ r
   eq1 = cong (r · 1r +_) (0-leftNullifies _) ∙∙ +-rid _ ∙∙ ·-rid _

   path : [ r · 1r + 0r · s , s · 1r , SsubMonoid .multClosed s∈S (SsubMonoid .containsOne) ]
        ≡ [ r , s , s∈S ]
   path = cong [_] (ΣPathP (eq1 , Σ≡Prop (λ x → ∈-isProp S' x) (·-rid _)))

 -ₗ_ : Rₛ → Rₛ
 -ₗ_ = SQ.rec squash/ -ₗ[] -ₗWellDef
  where
  -ₗ[] : R × S → Rₛ
  -ₗ[] (r , s) = [ - r , s ]

  -ₗWellDef : (a b : R × S) → a ≈' b → -ₗ[] a ≡ -ₗ[] b
  -ₗWellDef (r , s , _) (r' , s' , _) (u , p) = eq/ _ _ (u , path)
   where
   path : fst u · - r · s' ≡ fst u · - r' · s
   path = fst u · - r · s'   ≡⟨ cong (_· s') (-commutesWithRight-· _ _) ⟩
          - (fst u · r) · s' ≡⟨ -commutesWithLeft-· _ _ ⟩
          - (fst u · r · s') ≡⟨ cong -_ p ⟩
          - (fst u · r' · s) ≡⟨ sym (-commutesWithLeft-· _ _) ⟩
          - (fst u · r') · s ≡⟨ cong (_· s) (sym (-commutesWithRight-· _ _)) ⟩
          fst u · - r' · s   ∎

 +ₗ-rinv : (x : Rₛ) → x +ₗ (-ₗ x) ≡ 0ₗ
 +ₗ-rinv = SQ.elimProp (λ _ → squash/ _ _) +ₗ-rinv[]
  where
  +ₗ-rinv[] : (a : R × S) → ([ a ] +ₗ (-ₗ [ a ])) ≡ 0ₗ
  +ₗ-rinv[] (r , s , s∈S) = eq/ _ _ ((1r , SsubMonoid .containsOne) , path)
   where
   path : 1r · (r · s + - r · s) · 1r ≡ 1r · 0r · (s · s)
   path = 1r · (r · s + - r · s) · 1r   ≡⟨ cong (λ x → 1r · (r · s + x) · 1r) (-commutesWithLeft-· _ _) ⟩
          1r · (r · s + - (r · s)) · 1r ≡⟨ cong (λ x → 1r · x · 1r) (+-rinv _) ⟩
          1r · 0r · 1r                  ≡⟨ ·-rid _ ⟩
          1r · 0r                       ≡⟨ ·-lid _ ⟩
          0r                            ≡⟨ sym (0-leftNullifies _) ⟩
          0r · (s · s)                  ≡⟨ cong (_· (s · s)) (sym (·-lid _)) ⟩
          1r · 0r · (s · s)             ∎



 -- defining addition for truncated version is much more tedious:
 -- _+ₗ_ : S⁻¹R/ → S⁻¹R/ → S⁻¹R/
 -- _+ₗ_ = setQuotBinOp locRefl (_+ₚ_ , θ)
 --  where
 --  locRefl : isRefl _≈_
 --  locRefl _ = ∣ (1r , SsubMonoid .containsOne) , refl ∣

 --  _+ₚ_ : R × S → R × S → R × S
 --  (r₁ , s₁ , s₁∈S) +ₚ (r₂ , s₂ , s₂∈S) =
 --                      (r₁ · s₂ + r₂ · s₁) , (s₁ · s₂) , SsubMonoid .multClosed s₁∈S s₂∈S

 --  θ : (a a' b b' : R × S) → a ≈ a' → b ≈ b' → (a +ₚ b) ≈ (a' +ₚ b')
 --  θ a a' b b' = PT.rec (isPropΠ (λ _ →  propTruncIsProp)) (θ' a a' b b')
 --    where
 --    θ' : (a a' b b' : R × S) → Σ[ s ∈ S ] (fst s · fst a · fst (snd a') ≡ fst s · fst a' · fst (snd a))
 --                             → b ≈ b' → (a +ₚ b) ≈ (a' +ₚ b')
 --    θ' a a' b b' p = PT.rec propTruncIsProp (θ'' a a' b b' p)
 --       where
 --       θ'' : (a a' b b' : R × S)
 --           → Σ[ s ∈ S ] (fst s · fst a · fst (snd a') ≡ fst s · fst a' · fst (snd a))
 --           → Σ[ s ∈ S ] (fst s · fst b · fst (snd b') ≡ fst s · fst b' · fst (snd b))
 --           → (a +ₚ b) ≈ (a' +ₚ b')
 --       θ'' (r₁ , s₁ , s₁∈S) (r'₁ , s'₁ , s'₁∈S) (r₂ , s₂ , s₂∈S) (r'₂ , s'₂ , s'₂∈S) (s , p) (s' , q) =
 --        ∣ ((fst s · fst s') , SsubMonoid .multClosed (s .snd) (s' .snd)) , {!!} ∣


 -- Now for multiplication
 _·ₗ_ : Rₛ → Rₛ → Rₛ
 _·ₗ_ = setQuotBinOp locRefl _·ₚ_ θ
  where
  _·ₚ_ : R × S → R × S → R × S
  (r₁ , s₁ , s₁∈S) ·ₚ (r₂ , s₂ , s₂∈S) =
                      (r₁ · r₂) , ((s₁ · s₂) , SsubMonoid .multClosed s₁∈S s₂∈S)

  θ : (a a' b b' : R × S) → a ≈' a' → b ≈' b' → (a ·ₚ b) ≈' (a' ·ₚ b')
  θ (r₁ , s₁ , s₁∈S) (r'₁ , s'₁ , s'₁∈S) (r₂ , s₂ , s₂∈S) (r'₂ , s'₂ , s'₂∈S) (s , p) (s' , q) =
    ((fst s · fst s') , SsubMonoid .multClosed (s .snd) (s' .snd)) , path
    where
    path : fst s · fst s' · (r₁ · r₂) · (s'₁ · s'₂)
         ≡ fst s · fst s' · (r'₁ · r'₂) · (s₁ · s₂)
    path = fst s · fst s' · (r₁ · r₂) · (s'₁ · s'₂)
         ≡⟨ (λ i → ·-assoc (fst s · fst s') r₁ r₂ i · (s'₁ · s'₂)) ⟩
           fst s · fst s' · r₁ · r₂ · (s'₁ · s'₂)
         ≡⟨ (λ i → ·-assoc (fst s · fst s' · r₁ · r₂) s'₁ s'₂ i) ⟩
           fst s · fst s' · r₁ · r₂ · s'₁ · s'₂
         ≡⟨ (λ i → ·-assoc (fst s) (fst s') r₁ (~ i) · r₂ · s'₁ · s'₂) ⟩
           fst s · (fst s' · r₁) · r₂ · s'₁ · s'₂
         ≡⟨ (λ i → fst s · (·-comm (fst s') r₁ i) · r₂ · s'₁ · s'₂) ⟩
           fst s · (r₁ · fst s') · r₂ · s'₁ · s'₂
         ≡⟨ (λ i → ·-assoc (fst s) r₁  (fst s') i · r₂ · s'₁ · s'₂) ⟩
           fst s · r₁ · fst s' · r₂ · s'₁ · s'₂
         ≡⟨ (λ i → ·-assoc (fst s · r₁ · fst s') r₂ s'₁ (~ i) · s'₂) ⟩
           fst s · r₁ · fst s' · (r₂ · s'₁) · s'₂
         ≡⟨ (λ i → fst s · r₁ · fst s' · (·-comm r₂ s'₁ i) · s'₂) ⟩
           fst s · r₁ · fst s' · (s'₁ · r₂) · s'₂
         ≡⟨ (λ i → ·-assoc (fst s · r₁ · fst s') s'₁ r₂ i · s'₂) ⟩
           fst s · r₁ · fst s' · s'₁ · r₂ · s'₂
         ≡⟨ (λ i → ·-assoc (fst s · r₁) (fst s') s'₁ (~ i) · r₂ · s'₂) ⟩
           fst s · r₁ · (fst s' · s'₁) · r₂ · s'₂
         ≡⟨ (λ i → fst s · r₁ · (·-comm (fst s') s'₁ i) · r₂ · s'₂) ⟩
           fst s · r₁ · (s'₁ · fst s') · r₂ · s'₂
         ≡⟨ (λ i → ·-assoc (fst s · r₁) s'₁ (fst s') i · r₂ · s'₂) ⟩
           fst s · r₁ · s'₁ · fst s' · r₂ · s'₂
         ≡⟨ (λ i → ·-assoc (fst s · r₁ · s'₁) (fst s') r₂ (~ i) · s'₂) ⟩
           fst s · r₁ · s'₁ · (fst s' · r₂) · s'₂
         ≡⟨ (λ i → ·-assoc (fst s · r₁ · s'₁) (fst s' · r₂) s'₂ (~ i)) ⟩
           fst s · r₁ · s'₁ · (fst s' · r₂ · s'₂)
         ≡⟨ (λ i → (p i) · (q i)) ⟩
           fst s · r'₁ · s₁ · (fst s' · r'₂ · s₂)
         ≡⟨ (λ i → ·-assoc (fst s · r'₁ · s₁) (fst s' · r'₂) s₂ i) ⟩
           fst s · r'₁ · s₁ · (fst s' · r'₂) · s₂
         ≡⟨ (λ i → ·-assoc (fst s · r'₁ · s₁) (fst s') r'₂ i · s₂) ⟩
           fst s · r'₁ · s₁ · fst s' · r'₂ · s₂
         ≡⟨ (λ i → ·-assoc (fst s · r'₁) s₁ (fst s') (~ i) · r'₂ · s₂) ⟩
           fst s · r'₁ · (s₁ · fst s') · r'₂ · s₂
         ≡⟨ (λ i → fst s · r'₁ · (·-comm s₁ (fst s') i) · r'₂ · s₂) ⟩
           fst s · r'₁ · (fst s' · s₁) · r'₂ · s₂
         ≡⟨ (λ i → ·-assoc (fst s · r'₁) (fst s') s₁ i · r'₂ · s₂) ⟩
           fst s · r'₁ · fst s' · s₁ · r'₂ · s₂
         ≡⟨ (λ i → ·-assoc (fst s · r'₁ · fst s') s₁ r'₂ (~ i) · s₂) ⟩
           fst s · r'₁ · fst s' · (s₁ · r'₂) · s₂
         ≡⟨ (λ i → fst s · r'₁ · fst s' · (·-comm s₁ r'₂ i) · s₂) ⟩
           fst s · r'₁ · fst s' · (r'₂ · s₁) · s₂
         ≡⟨ (λ i → ·-assoc (fst s · r'₁ · fst s') r'₂ s₁ i · s₂) ⟩
           fst s · r'₁ · fst s' · r'₂ · s₁ · s₂
         ≡⟨ (λ i → ·-assoc (fst s) r'₁ (fst s') (~ i) · r'₂ · s₁ · s₂) ⟩
           fst s · (r'₁ · fst s') · r'₂ · s₁ · s₂
         ≡⟨ (λ i → fst s · (·-comm r'₁ (fst s') i) · r'₂ · s₁ · s₂) ⟩
           fst s · (fst s' · r'₁) · r'₂ · s₁ · s₂
         ≡⟨ (λ i → ·-assoc (fst s) (fst s') r'₁ i · r'₂ · s₁ · s₂) ⟩
           fst s · fst s' · r'₁ · r'₂ · s₁ · s₂
         ≡⟨ (λ i → ·-assoc (fst s · fst s' · r'₁ · r'₂) s₁ s₂ (~ i)) ⟩
           fst s · fst s' · r'₁ · r'₂ · (s₁ · s₂)
         ≡⟨ (λ i → ·-assoc (fst s · fst s') r'₁ r'₂ (~ i) · (s₁ · s₂)) ⟩
           fst s · fst s' · (r'₁ · r'₂) · (s₁ · s₂) ∎




 -- checking laws for multiplication
 1ₗ : Rₛ
 1ₗ = [ 1r , 1r , SsubMonoid .containsOne ]

 ·ₗ-assoc : (x y z : Rₛ) → x ·ₗ (y ·ₗ z) ≡ (x ·ₗ y) ·ₗ z
 ·ₗ-assoc = SQ.elimProp3 (λ _ _ _ → squash/ _ _) ·ₗ-assoc[]
   where
   ·ₗ-assoc[] : (a b c : R × S) → [ a ] ·ₗ ([ b ] ·ₗ [ c ]) ≡ ([ a ] ·ₗ [ b ]) ·ₗ [ c ]
   ·ₗ-assoc[] (r , s , s∈S) (r' , s' , s'∈S) (r'' , s'' , s''∈S) =
              cong [_] (ΣPathP ((·-assoc _ _ _) , Σ≡Prop (λ x → ∈-isProp S' x) (·-assoc _ _ _)))

 ·ₗ-rid : (x : Rₛ) → x ·ₗ 1ₗ ≡ x
 ·ₗ-rid = SQ.elimProp (λ _ → squash/ _ _) ·ₗ-rid[]
   where
   ·ₗ-rid[] : (a : R × S) → ([ a ] ·ₗ 1ₗ) ≡ [ a ]
   ·ₗ-rid[] (r , s , s∈S) = cong [_] (ΣPathP ((·-rid _) , Σ≡Prop (λ x → ∈-isProp S' x) (·-rid _)))


 ·ₗ-rdist-+ₗ : (x y z : Rₛ) → x ·ₗ (y +ₗ z) ≡ (x ·ₗ y) +ₗ (x ·ₗ z)
 ·ₗ-rdist-+ₗ = SQ.elimProp3 (λ _ _ _ → squash/ _ _) ·ₗ-rdist-+ₗ[]
   where
   ·ₗ-rdist-+ₗ[] : (a b c : R × S) → [ a ] ·ₗ ([ b ] +ₗ [ c ]) ≡ ([ a ] ·ₗ [ b ]) +ₗ ([ a ] ·ₗ [ c ])
   ·ₗ-rdist-+ₗ[] (r , s , s∈S) (r' , s' , s'∈S) (r'' , s'' , s''∈S) = {!!}


 ·ₗ-comm : (x y : Rₛ) → x ·ₗ y ≡ y ·ₗ x
 ·ₗ-comm = SQ.elimProp2 (λ _ _ → squash/ _ _) ·ₗ-comm[]
   where
   ·ₗ-comm[] : (a b : R × S) → [ a ] ·ₗ [ b ] ≡ [ b ] ·ₗ [ a ]
   ·ₗ-comm[] (r , s , s∈S) (r' , s' , s'∈S) =
             cong [_] (ΣPathP ((·-comm _ _) , Σ≡Prop (λ x → ∈-isProp S' x) (·-comm _ _)))

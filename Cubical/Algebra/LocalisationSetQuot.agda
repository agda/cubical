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

 _+ₗ_ : Rₛ → Rₛ → Rₛ
 _+ₗ_ = setQuotBinOp locRefl (_+ₚ_ , θ)
  where
  locRefl : isRefl _≈'_
  locRefl _ = (1r , SsubMonoid .containsOne) , refl

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
         ≡⟨ {!!} ⟩
           fst s · fst s' · r'₁ · s'₂ · (s₁ · s₂) + fst s · fst s' · r'₂ · s'₁ · (s₁ · s₂)
         ≡⟨ (λ i → ·-assoc (fst s · fst s') r'₁ s'₂ (~ i) · (s₁ · s₂)
                 + ·-assoc (fst s · fst s') r'₂ s'₁ (~ i) · (s₁ · s₂)) ⟩
           fst s · fst s' · (r'₁ · s'₂) · (s₁ · s₂) + fst s · fst s' · (r'₂ · s'₁) · (s₁ · s₂)
         ≡⟨ sym (·-ldist-+ _ _ _) ⟩
           (fst s · fst s' · (r'₁ · s'₂)  + fst s · fst s' · (r'₂ · s'₁)) · (s₁ · s₂)
         ≡⟨ cong (_· (s₁ · s₂)) (sym (·-rdist-+ _ _ _)) ⟩
           fst s · fst s' · (r'₁ · s'₂ + r'₂ · s'₁) · (s₁ · s₂) ∎



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

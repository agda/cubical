{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.LocalisationSetQuot where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Transport
open import Cubical.Functions.FunExtEquiv

import Cubical.Data.Empty as ⊥
open import Cubical.Data.Bool
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_ ; +-comm to +ℕ-comm ; +-assoc to +ℕ-assoc ; ·-assoc to ·ℕ-assoc ; ·-comm to ·ℕ-comm)
open import Cubical.Data.Vec
open import Cubical.Data.Sigma.Base
open import Cubical.Data.Sigma.Properties
open import Cubical.Data.FinData
open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary

open import Cubical.Algebra.Group
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Integers renaming (BiInvIntAsCommRing to ℤAsCommRing)

open import Cubical.HITs.Ints.BiInvInt renaming (BiInvInt to ℤ ; _+_ to _+ℤ_ ; _·_ to _·ℤ_ ; -_ to -ℤ_ ; +-assoc to +ℤ-assoc ; +-comm to +ℤ-comm ; ·-assoc to ·ℤ-assoc ; ·-comm to ·ℤ-comm)
open import Cubical.HITs.SetQuotients as SQ
open import Cubical.HITs.PropositionalTruncation as PT

open Iso

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ


record isSubMonoid (R' : CommRing {ℓ}) (S' : ℙ (R' .fst)) : Type ℓ where
 constructor
   submonoid
 field
   containsOne : (R' .snd .CommRingStr.1r) ∈ S'
   multClosed : ∀ {s t} → s ∈ S' → t ∈ S' → (R' .snd .CommRingStr._·_ s t) ∈ S'

module Loc (R' : CommRing {ℓ}) (S' : ℙ (R' .fst)) (SsubMonoid : isSubMonoid R' S') where
 open isSubMonoid
 R = R' .fst
 open CommRingStr (R' .snd)
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
 +ₗ-assoc : (x y z : Rₛ) → x +ₗ (y +ₗ z) ≡ (x +ₗ y) +ₗ z
 +ₗ-assoc = SQ.elimProp3 (λ _ _ _ → squash/ _ _) +ₗ-assoc[]
  where
  +ₗ-assoc[] : (a b c : R × S) → [ a ] +ₗ ([ b ] +ₗ [ c ]) ≡ ([ a ] +ₗ [ b ]) +ₗ [ c ]
  +ₗ-assoc[] (r , s , s∈S) (r' , s' , s'∈S) (r'' , s'' , s''∈S) =
             cong [_] (ΣPathP (path , Σ≡Prop (λ x → ∈-isProp S' x) (·-assoc _ _ _)))
   where
   path : r · (s' · s'') + (r' · s'' + r'' · s') · s
        ≡ (r · s' + r' · s) · s'' + r'' · (s · s')
   path = r · (s' · s'') + (r' · s'' + r'' · s') · s
        ≡⟨ (λ i → ·-assoc r s' s'' i + ·-ldist-+ (r' · s'') (r'' · s') s i) ⟩
          r · s' · s'' + (r' · s'' · s + r'' · s' · s)
        ≡⟨ +-assoc _ _ _ ⟩
          r · s' · s'' + r' · s'' · s + r'' · s' · s
        ≡⟨ (λ i → r · s' · s'' + ·-assoc r' s'' s (~ i) + ·-assoc r'' s' s (~ i)) ⟩
          r · s' · s'' + r' · (s'' · s) + r'' · (s' · s)
        ≡⟨ (λ i → r · s' · s'' + r' · (·-comm s'' s i) + r'' · (·-comm s' s i)) ⟩
          r · s' · s'' + r' · (s · s'') + r'' · (s · s')
        ≡⟨ (λ i → r · s' · s'' + ·-assoc r' s  s'' i + r'' · (s · s')) ⟩
          r · s' · s'' + r' · s · s'' + r'' · (s · s')
        ≡⟨ (λ i → ·-ldist-+ (r · s') (r' · s) s'' (~ i) + r'' · (s · s')) ⟩
          (r · s' + r' · s) · s'' + r'' · (s · s') ∎

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


 +ₗ-comm : (x y : Rₛ) → x +ₗ y ≡ y +ₗ x
 +ₗ-comm = SQ.elimProp2 (λ _ _ → squash/ _ _) +ₗ-comm[]
  where
  +ₗ-comm[] : (a b : R × S) → ([ a ] +ₗ [ b ]) ≡ ([ b ] +ₗ [ a ])
  +ₗ-comm[] (r , s , s∈S) (r' , s' , s'∈S) =
            cong [_] (ΣPathP ((+-comm _ _) , Σ≡Prop (λ x → ∈-isProp S' x) (·-comm _ _)))

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
   ·ₗ-rdist-+ₗ[] (r , s , s∈S) (r' , s' , s'∈S) (r'' , s'' , s''∈S) =
      eq/ _ _ ((1r , (SsubMonoid .containsOne)) , path)
      where
      path : 1r · (r · (r' · s'' + r'' · s')) · (s · s' · (s · s''))
           ≡ 1r · (r · r' · (s · s'') + r · r'' · (s · s')) · (s · (s' · s''))
      path = 1r · (r · (r' · s'' + r'' · s')) · (s · s' · (s · s''))
           ≡⟨ (λ i → ·-lid (r · (r' · s'' + r'' · s')) i · (s · s' · (s · s''))) ⟩
             r · (r' · s'' + r'' · s') · (s · s' · (s · s''))
           ≡⟨ (λ i → ·-rdist-+ r (r' · s'') (r'' · s') i · (s · s' · (s · s''))) ⟩
             (r · (r' · s'') + r · (r'' · s')) · (s · s' · (s · s''))
           ≡⟨ (λ i → (·-assoc r r' s'' i + ·-assoc r r'' s' i) · (s · s' · (s · s''))) ⟩
             (r · r' · s'' + r · r'' · s') · (s · s' · (s · s''))
           ≡⟨ (λ i → (r · r' · s'' + r · r'' · s') · (·-assoc s s' (s · s'') (~ i))) ⟩
             (r · r' · s'' + r · r'' · s') · (s · (s' · (s · s'')))
           ≡⟨ (λ i → ·-assoc (r · r' · s'' + r · r'' · s') s (s' · (s · s'')) i) ⟩
             (r · r' · s'' + r · r'' · s') · s · (s' · (s · s''))
           ≡⟨ (λ i → ·-ldist-+ (r · r' · s'') (r · r'' · s') s i · (·-assoc s' s s'' i)) ⟩
             (r · r' · s'' · s + r · r'' · s' · s) · (s' · s · s'')
           ≡⟨ (λ i → (·-assoc (r · r') s'' s (~ i) + ·-assoc (r · r'') s' s (~ i)) · ((·-comm s' s i) · s'')) ⟩
             (r · r' · (s'' · s) + r · r'' · (s' · s)) · (s · s' · s'')
           ≡⟨ (λ i → (r · r' · (·-comm s'' s i) + r · r'' · (·-comm s' s i)) · (·-assoc s s' s'' (~ i))) ⟩
             (r · r' · (s · s'') + r · r'' · (s · s')) · (s · (s' · s''))
           ≡⟨ (λ i → ·-lid (r · r' · (s · s'') + r · r'' · (s · s')) (~ i) · (s · (s' · s''))) ⟩
             1r · (r · r' · (s · s'') + r · r'' · (s · s')) · (s · (s' · s'')) ∎


 ·ₗ-comm : (x y : Rₛ) → x ·ₗ y ≡ y ·ₗ x
 ·ₗ-comm = SQ.elimProp2 (λ _ _ → squash/ _ _) ·ₗ-comm[]
   where
   ·ₗ-comm[] : (a b : R × S) → [ a ] ·ₗ [ b ] ≡ [ b ] ·ₗ [ a ]
   ·ₗ-comm[] (r , s , s∈S) (r' , s' , s'∈S) =
             cong [_] (ΣPathP ((·-comm _ _) , Σ≡Prop (λ x → ∈-isProp S' x) (·-comm _ _)))



 -- Commutative ring structure on Rₛ
 RₛAsCommRing : CommRing
 RₛAsCommRing = makeCommRing 0ₗ 1ₗ _+ₗ_ _·ₗ_ -ₗ_ squash/ +ₗ-assoc +ₗ-rid +ₗ-rinv +ₗ-comm
                                                         ·ₗ-assoc ·ₗ-rid ·ₗ-rdist-+ₗ ·ₗ-comm


-- Test: (R[1/f])[1/g] ≡ R[1/fg]
module invertEl (R' : CommRing {ℓ}) where
 open isSubMonoid
 R = R' .fst
 open CommRingStr (R' .snd)
 open Theory (CommRing→Ring R')


 _^_ : R → ℕ → R
 f ^ zero = 1r
 f ^ suc n = f · (f ^ n)

 infix 9 _^_

 ·-of-^-is-^-of-+ : (f : R) (m n : ℕ) → (f ^ m) · (f ^ n) ≡ f ^ (m +ℕ n)
 ·-of-^-is-^-of-+ f zero n = ·-lid _
 ·-of-^-is-^-of-+ f (suc m) n = sym (·-assoc _ _ _) ∙ cong (f ·_) (·-of-^-is-^-of-+ f m n)

 ^-ldist-· : (f g : R) (n : ℕ) → (f · g) ^ n ≡ (f ^ n) · (g ^ n)
 ^-ldist-· f g zero = sym (·-lid 1r)
 ^-ldist-· f g (suc n) = path
  where
  path : f · g · ((f · g) ^ n) ≡ f · (f ^ n) · (g · (g ^ n))
  path = f · g · ((f · g) ^ n) ≡⟨ cong (f · g ·_) (^-ldist-· f g n) ⟩
         f · g · ((f ^ n) · (g ^ n)) ≡⟨ ·-assoc _ _ _ ⟩
         f · g · (f ^ n) · (g ^ n) ≡⟨ cong (_· (g ^ n)) (sym (·-assoc _ _ _)) ⟩
         f · (g · (f ^ n)) · (g ^ n) ≡⟨ cong (λ r → (f · r) · (g ^ n)) (·-comm _ _) ⟩
         f · ((f ^ n) · g) · (g ^ n) ≡⟨ cong (_· (g ^ n)) (·-assoc _ _ _) ⟩
         f · (f ^ n) · g · (g ^ n) ≡⟨ sym (·-assoc _ _ _) ⟩
         f · (f ^ n) · (g · (g ^ n)) ∎

 [_ⁿ|n≥0] : R → ℙ R
 [ f ⁿ|n≥0] g = (∃[ n ∈ ℕ ] g ≡ f ^ n) , propTruncIsProp
 -- Σ[ n ∈ ℕ ] (s ≡ f ^ n) × (∀ m → s ≡ f ^ m → n ≤ m) maybe better, this isProp:
 -- (n,s≡fⁿ,p) (m,s≡fᵐ,q) then n≤m by p and  m≤n by q => n≡m

 powersFormSubMonoid : (f : R) → isSubMonoid R' [ f ⁿ|n≥0]
 powersFormSubMonoid f .containsOne = ∣ zero , refl ∣
 powersFormSubMonoid f .multClosed =
             PT.map2 λ (m , p) (n , q) → (m +ℕ n) , (λ i → (p i) · (q i)) ∙ ·-of-^-is-^-of-+ f m n


 R[1/_] : R → Type ℓ
 R[1/ f ] = Loc.Rₛ R' [ f ⁿ|n≥0] (powersFormSubMonoid f)


 R[1/_]AsCommRing : R → CommRing {ℓ}
 R[1/ f ]AsCommRing = Loc.RₛAsCommRing R' [ f ⁿ|n≥0] (powersFormSubMonoid f)


module check (R' : CommRing {ℓ}) (f g : (R' .fst)) where
 open isSubMonoid
 open CommRingStr (R' .snd)
 open Theory (CommRing→Ring R')
 open invertEl R' hiding (R)
 open CommRingStr (R[1/ f ]AsCommRing .snd) renaming (_·_ to _·ᶠ_ ; 1r to 1ᶠ)
                                            hiding (_+_ ; ·-lid ; ·-rid ; ·-assoc ; ·-comm)


 R = R' .fst
 R[1/fg] = invertEl.R[1/_] R' (f · g)
 R[1/f][1/g] = invertEl.R[1/_] (invertEl.R[1/_]AsCommRing R' f)
                               [ g , 1r , powersFormSubMonoid f .containsOne ]
 R[1/f][1/g]AsCommRing = invertEl.R[1/_]AsCommRing (invertEl.R[1/_]AsCommRing R' f)
                               [ g , 1r , powersFormSubMonoid f .containsOne ]

 -- prove R[1/fg] ≃ R[1/f][1/g] and then check ringhom
 indhelper : ∀ n → [ (g ^ n) , 1r , ∣ 0 , (λ _ → 1r) ∣ ] ≡
     (R[1/ f ]AsCommRing invertEl.^ [ g , 1r , powersFormSubMonoid f .containsOne ]) n
 indhelper zero = refl
 indhelper (suc n) =
       eq/ _ _ ((1r , powersFormSubMonoid f .containsOne) , cong (1r · (g · (g ^ n)) ·_) (·-lid 1r))
     ∙ cong ([ g , 1r , powersFormSubMonoid f .containsOne ] ·ᶠ_) (indhelper n)

 φ : R[1/fg] → R[1/f][1/g]
 φ = SQ.rec squash/ ϕ ϕcoh
   where
   open Loc R' [ (f · g) ⁿ|n≥0] (powersFormSubMonoid (f · g)) hiding (R ; φ)

   curriedϕΣ : (r s : R) → Σ[ n ∈ ℕ ] s ≡ (f · g) ^ n → R[1/f][1/g]
   curriedϕΣ r s (n , s≡fg^n) =
    [ [ r , (f ^ n) , ∣ n , refl ∣ ] , [ (g ^ n) , 1r , ∣ 0 , refl ∣ ] , ∣ n , indhelper n ∣ ]

   curriedϕ : (r s : R) → ∃[ n ∈ ℕ ] s ≡ (f · g) ^ n → R[1/f][1/g]
   curriedϕ r s = elim→Set (λ _ → squash/) (curriedϕΣ r s) coh
    where
    coh : (x y : Σ[ n ∈ ℕ ] s ≡ (f · g) ^ n) → curriedϕΣ r s x ≡ curriedϕΣ r s y
    coh (n , s≡fg^n) (m , s≡fg^m) = eq/ _ _ ((1ᶠ , ∣ 0 , refl ∣) ,
                                    eq/ _ _ ((1r , powersFormSubMonoid f .containsOne) , path))
     where
     path : 1r · (1r · r · (g ^ m)) · (1r · (f ^ m) · 1r)
          ≡ 1r · (1r · r · (g ^ n)) · (1r · (f ^ n) · 1r)
     path = 1r · (1r · r · (g ^ m)) · (1r · (f ^ m) · 1r)
          ≡⟨ (λ i → ·-lid ((·-lid r i) · (g ^ m)) i · (·-rid (·-lid (f ^ m) i) i)) ⟩
            r · g ^ m · f ^ m
          ≡⟨ sym (·-assoc _ _ _) ⟩
            r · (g ^ m · f ^ m)
          ≡⟨ cong (r ·_) (sym (^-ldist-· g f m)) ⟩
            r · ((g · f) ^ m)
          ≡⟨ cong (λ x → r · (x ^ m)) (·-comm _ _) ⟩
            r · ((f · g) ^ m)
          ≡⟨ cong (r ·_) ((sym s≡fg^m) ∙ s≡fg^n) ⟩
            r · ((f · g) ^ n)
          ≡⟨ cong (λ x → r · (x ^ n)) (·-comm _ _) ⟩
            r · ((g · f) ^ n)
          ≡⟨ cong (r ·_) (^-ldist-· g f n) ⟩
            r · (g ^ n · f ^ n)
          ≡⟨ ·-assoc _ _ _ ⟩
            r · g ^ n · f ^ n
          ≡⟨ (λ i → ·-lid ((·-lid r (~ i)) · (g ^ n)) (~ i) · (·-rid (·-lid (f ^ n) (~ i)) (~ i))) ⟩
            1r · (1r · r · (g ^ n)) · (1r · (f ^ n) · 1r) ∎

   ϕ : R × S → R[1/f][1/g]
   ϕ (r , s , |n,s≡fg^n|) = curriedϕ r s |n,s≡fg^n|
   -- λ (r / (fg)ⁿ) → ((r / fⁿ) /gⁿ)

   curriedϕcohΣ : (r s r' s' u : R) → (p : u · r · s' ≡ u · r' · s)
                                    → (α : Σ[ n ∈ ℕ ] s ≡ (f · g) ^ n)
                                    → (β : Σ[ m ∈ ℕ ] s' ≡ (f · g) ^ m)
                                    → (γ : Σ[ l ∈ ℕ ] u ≡ (f · g) ^ l)
                                    → ϕ (r , s , ∣ α ∣) ≡ ϕ (r' , s' , ∣ β ∣)
   curriedϕcohΣ r s r' s' u p (n , s≡fgⁿ) (m , s'≡fgᵐ) (l , u≡fgˡ) =
    eq/ _ _ (([ (g ^ l) , 1r , powersFormSubMonoid f .containsOne ] , ∣ l , indhelper l ∣) ,
    eq/ _ _ ((f ^ l , ∣ l , refl ∣) , path))
    where
    path : f ^ l · (g ^ l · transp (λ i → R) i0 r · transp (λ i → R) i0 (g ^ m))
                 · (1r · transp (λ i → R) i0 (f ^ m) · transp (λ i → R) i0 1r)
         ≡ f ^ l · (g ^ l · transp (λ i → R) i0 r' · transp (λ i → R) i0 (g ^ n))
                 · (1r · transp (λ i → R) i0 (f ^ n) · transp (λ i → R) i0 1r)
    path = f ^ l · (g ^ l · transp (λ i → R) i0 r · transp (λ i → R) i0 (g ^ m))
                 · (1r · transp (λ i → R) i0 (f ^ m) · transp (λ i → R) i0 1r)
         ≡⟨ (λ i → f ^ l · (g ^ l · transportRefl r i · transportRefl (g ^ m) i)
                         · (1r · transportRefl (f ^ m) i · transportRefl 1r i)) ⟩
           f ^ l · (g ^ l · r · g ^ m) · (1r · f ^ m · 1r)
         ≡⟨ (λ i → ·-assoc (f ^ l) ((g ^ l) · r) (g ^ m) i · ·-rid (1r · (f ^ m)) i) ⟩
           f ^ l · (g ^ l · r) · g ^ m · (1r · f ^ m)
         ≡⟨ (λ i → ·-assoc (f ^ l) (g ^ l) r i · g ^ m ·  ·-lid (f ^ m) i) ⟩
           f ^ l · g ^ l · r · g ^ m · f ^ m
         ≡⟨ sym (·-assoc _ _ _) ⟩
           f ^ l · g ^ l · r · (g ^ m · f ^ m)
         ≡⟨ (λ i → ^-ldist-· f g l (~ i) · r · ^-ldist-· g f m (~ i)) ⟩
           (f · g) ^ l · r · (g · f) ^ m
         ≡⟨ cong (λ x → (f · g) ^ l · r · x ^ m) (·-comm _ _) ⟩
           (f · g) ^ l · r · (f · g) ^ m
         ≡⟨ (λ i → u≡fgˡ (~ i) · r · s'≡fgᵐ (~ i)) ⟩
           u · r · s'
         ≡⟨ p ⟩
           u · r' · s
         ≡⟨ (λ i → u≡fgˡ i · r' · s≡fgⁿ i) ⟩
           (f · g) ^ l · r' · (f · g) ^ n
         ≡⟨ cong (λ x → (f · g) ^ l · r' · x ^ n) (·-comm _ _) ⟩
           (f · g) ^ l · r' · (g · f) ^ n
         ≡⟨ (λ i → ^-ldist-· f g l i · r' · ^-ldist-· g f n i) ⟩
           f ^ l · g ^ l · r' · (g ^ n · f ^ n)
         ≡⟨ ·-assoc _ _ _ ⟩
           f ^ l · g ^ l · r' · g ^ n · f ^ n
         ≡⟨ (λ i → ·-assoc (f ^ l) (g ^ l) r' (~ i) · g ^ n ·  ·-lid (f ^ n) (~ i)) ⟩
           f ^ l · (g ^ l · r') · g ^ n · (1r · f ^ n)
         ≡⟨ (λ i → ·-assoc (f ^ l) ((g ^ l) · r') (g ^ n) (~ i) · ·-rid (1r · (f ^ n)) (~ i)) ⟩
           f ^ l · (g ^ l · r' · g ^ n) · (1r · f ^ n · 1r)
         ≡⟨ (λ i → f ^ l · (g ^ l · transportRefl r' (~ i) · transportRefl (g ^ n) (~ i))
                         · (1r · transportRefl (f ^ n) (~ i) · transportRefl 1r (~ i))) ⟩
           f ^ l · (g ^ l · transp (λ i → R) i0 r' · transp (λ i → R) i0 (g ^ n))
                 · (1r · transp (λ i → R) i0 (f ^ n) · transp (λ i → R) i0 1r) ∎

   curriedϕcoh : (r s r' s' u : R) → (p : u · r · s' ≡ u · r' · s)
                                   → (α : ∃[ n ∈ ℕ ] s ≡ (f · g) ^ n)
                                   → (β : ∃[ m ∈ ℕ ] s' ≡ (f · g) ^ m)
                                   → (γ : ∃[ l ∈ ℕ ] u ≡ (f · g) ^ l)
                                   → ϕ (r , s , α) ≡ ϕ (r' , s' , β)
   curriedϕcoh r s r' s' u p = PT.elim (λ _ → isPropΠ2 (λ _ _ → squash/ _ _))
                         λ α → PT.elim (λ _ → isPropΠ (λ _ → squash/ _ _))
                         λ β → PT.rec (squash/ _ _)
                         λ γ →  curriedϕcohΣ r s r' s' u p α β γ

   ϕcoh : (a b : R × S) → a ≈' b → ϕ a ≡ ϕ b
   ϕcoh (r , s , α) (r' , s' , β) ((u , γ) , p) =  curriedϕcoh r s r' s' u p α β γ


 -- TODO:
 -- ψ : R[1/f][1/g] → R[1/fg]
 -- η : section φ ψ
 -- ε : retract φ ψ
 -- prove that φ is ring hom




module φtestℤ where
 1z : ℤ
 1z = suc zero

 2z : ℤ
 2z = suc (suc zero)

 3z : ℤ
 3z = suc (suc (suc zero))

 4z = 2z ·ℤ 2z

 5z : ℤ
 5z = suc ( suc (suc (suc (suc zero))))

 9z = 3z ·ℤ 3z

 6z = 2z ·ℤ 3z
 36z = 6z ·ℤ 6z


 open isSubMonoid
 open invertEl ℤAsCommRing
 open check ℤAsCommRing 2z 3z

 ℤ[1/6] = R[1/fg]
 ℤ[1/2][1/3] = R[1/f][1/g]

 5/36 : ℤ[1/6]
 5/36 = [ 5z , 36z , ∣ 2 , refl ∣ ]
 -- ∣ 2 , refl ∣ is proof that 36 is in the set of powers of 6

 test :  ℤ[1/2][1/3]
 test = [ [ 5z , 4z , ∣ 2 , refl ∣ ] ,
          [ 9z , 1z , powersFormSubMonoid 2z .containsOne ] , ∣ 2 , indhelper 2 ∣ ]

 -- not true !!!
 -- _ : test ≡ φ 5/36
 -- _ = refl


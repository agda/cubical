-- We define the localisation of a commutative ring
-- at a multiplicatively closed subset and show that it
-- has a commutative ring structure.

{-# OPTIONS --cubical --no-import-sorts --safe --experimental-lossy-unification #-}
module Cubical.Algebra.CommRing.Localisation.Base where

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
open import Cubical.Data.Nat renaming ( _+_ to _+ℕ_ ; _·_ to _·ℕ_
                                      ; +-comm to +ℕ-comm ; +-assoc to +ℕ-assoc
                                      ; ·-assoc to ·ℕ-assoc ; ·-comm to ·ℕ-comm)
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

open import Cubical.HITs.SetQuotients as SQ
open import Cubical.HITs.PropositionalTruncation as PT

open Iso

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ


-- A multiplicatively closed subset is assumed to contain 1
record isMultClosedSubset (R' : CommRing {ℓ}) (S' : ℙ (R' .fst)) : Type ℓ where
 constructor
   multclosedsubset
 field
   containsOne : (R' .snd .CommRingStr.1r) ∈ S'
   multClosed : ∀ {s t} → s ∈ S' → t ∈ S' → (R' .snd .CommRingStr._·_ s t) ∈ S'

module Loc (R' : CommRing {ℓ}) (S' : ℙ (R' .fst)) (SMultClosedSubset : isMultClosedSubset R' S') where
 open isMultClosedSubset
 private R = R' .fst
 open CommRingStr (R' .snd)
 open Theory (CommRing→Ring R')
 open CommTheory R'

 S = Σ[ s ∈ R ] (s ∈ S')

 -- We define the localisation of R by S by quotienting by the following relation:
 _≈_ : R × S → R × S → Type ℓ
 (r₁ , s₁) ≈ (r₂ , s₂) = Σ[ s ∈ S ] (fst s · r₁ · fst s₂ ≡ fst s · r₂ · fst s₁)

 S⁻¹R = (R × S) / _≈_

 -- now define addition for S⁻¹R
 open BinaryRelation

 locRefl : isRefl _≈_
 locRefl _ = (1r , SMultClosedSubset .containsOne) , refl

 locSym : isSym _≈_
 locSym (r , s , s∈S') (r' , s' , s'∈S') (u , p) = u , sym p

 locTrans : isTrans _≈_
 locTrans (r , s , s∈S') (r' , s' , s'∈S') (r'' , s'' , s''∈S') ((u , u∈S') , p) ((v , v∈S') , q) =
   ((u · v · s') , SMultClosedSubset .multClosed (SMultClosedSubset .multClosed u∈S' v∈S') s'∈S')
   , path
  where
  path : u · v · s' · r · s'' ≡ u · v · s' · r'' · s
  path = u · v · s' · r · s''   ≡⟨ cong (_· s'') (·-commAssocr _ _ _) ⟩
         u · v · r · s' · s''   ≡⟨ cong (λ x → x · s' · s'') (·-commAssocr _ _ _) ⟩
         u · r · v · s' · s''   ≡⟨ cong (_· s'') (·-commAssocr _ _ _) ⟩
         u · r · s' · v · s''   ≡⟨ cong (λ x → x · v · s'') p ⟩
         u · r' · s · v · s''   ≡⟨ cong (λ x → x · v · s'') (·-commAssocr _ _ _) ⟩
         u · s · r' · v · s''   ≡⟨ cong (_· s'') (·-commAssocr _ _ _) ⟩
         u · s · v · r' · s''   ≡⟨ cong (_· s'') (sym (·-assoc _ _ _)) ⟩
         u · s · (v · r') · s'' ≡⟨ sym (·-assoc _ _ _) ⟩
         u · s · (v · r' · s'') ≡⟨ cong (u · s ·_) q ⟩
         u · s · (v · r'' · s') ≡⟨ ·-assoc _ _ _ ⟩
         u · s · (v · r'') · s' ≡⟨ cong (_· s') (·-commAssocSwap _ _ _ _) ⟩
         u · v · (s · r'') · s' ≡⟨ sym (·-assoc _ _ _) ⟩
         u · v · (s · r'' · s') ≡⟨ cong (u · v ·_) (·-commAssocr2 _ _ _) ⟩
         u · v · (s' · r'' · s) ≡⟨ ·-assoc _ _ _ ⟩
         u · v · (s' · r'') · s ≡⟨ cong (_· s) (·-assoc _ _ _) ⟩
         u · v · s' · r'' · s   ∎

 locIsEquivRel : isEquivRel _≈_
 isEquivRel.reflexive locIsEquivRel = locRefl
 isEquivRel.symmetric locIsEquivRel = locSym
 isEquivRel.transitive locIsEquivRel = locTrans

 _+ₗ_ : S⁻¹R → S⁻¹R → S⁻¹R
 _+ₗ_ = setQuotBinOp locRefl _+ₚ_ θ
  where
  _+ₚ_ : R × S → R × S → R × S
  (r₁ , s₁ , s₁∈S) +ₚ (r₂ , s₂ , s₂∈S) =
                      (r₁ · s₂ + r₂ · s₁) , (s₁ · s₂) , SMultClosedSubset .multClosed s₁∈S s₂∈S

  θ : (a a' b b' : R × S) → a ≈ a' → b ≈ b' → (a +ₚ b) ≈ (a' +ₚ b')
  θ (r₁ , s₁ , s₁∈S) (r'₁ , s'₁ , s'₁∈S) (r₂ , s₂ , s₂∈S) (r'₂ , s'₂ , s'₂∈S) (s , p) (s' , q) =
    ((fst s · fst s') , SMultClosedSubset .multClosed (s .snd) (s' .snd)) , path
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
 +ₗ-assoc : (x y z : S⁻¹R) → x +ₗ (y +ₗ z) ≡ (x +ₗ y) +ₗ z
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

 0ₗ : S⁻¹R
 0ₗ = [ 0r , 1r , SMultClosedSubset .containsOne ]

 +ₗ-rid : (x : S⁻¹R) → x +ₗ 0ₗ ≡ x
 +ₗ-rid = SQ.elimProp (λ _ → squash/ _ _) +ₗ-rid[]
  where
  +ₗ-rid[] : (a : R × S) → [ a ] +ₗ 0ₗ ≡ [ a ]
  +ₗ-rid[] (r , s , s∈S) = path
   where
   eq1 : r · 1r + 0r · s ≡ r
   eq1 = cong (r · 1r +_) (0-leftNullifies _) ∙∙ +-rid _ ∙∙ ·-rid _

   path : [ r · 1r + 0r · s , s · 1r , SMultClosedSubset .multClosed s∈S
                                      (SMultClosedSubset .containsOne) ]
        ≡ [ r , s , s∈S ]
   path = cong [_] (ΣPathP (eq1 , Σ≡Prop (λ x → ∈-isProp S' x) (·-rid _)))

 -ₗ_ : S⁻¹R → S⁻¹R
 -ₗ_ = SQ.rec squash/ -ₗ[] -ₗWellDef
  where
  -ₗ[] : R × S → S⁻¹R
  -ₗ[] (r , s) = [ - r , s ]

  -ₗWellDef : (a b : R × S) → a ≈ b → -ₗ[] a ≡ -ₗ[] b
  -ₗWellDef (r , s , _) (r' , s' , _) (u , p) = eq/ _ _ (u , path)
   where
   path : fst u · - r · s' ≡ fst u · - r' · s
   path = fst u · - r · s'   ≡⟨ cong (_· s') (-commutesWithRight-· _ _) ⟩
          - (fst u · r) · s' ≡⟨ -commutesWithLeft-· _ _ ⟩
          - (fst u · r · s') ≡⟨ cong -_ p ⟩
          - (fst u · r' · s) ≡⟨ sym (-commutesWithLeft-· _ _) ⟩
          - (fst u · r') · s ≡⟨ cong (_· s) (sym (-commutesWithRight-· _ _)) ⟩
          fst u · - r' · s   ∎

 +ₗ-rinv : (x : S⁻¹R) → x +ₗ (-ₗ x) ≡ 0ₗ
 +ₗ-rinv = SQ.elimProp (λ _ → squash/ _ _) +ₗ-rinv[]
  where
  +ₗ-rinv[] : (a : R × S) → ([ a ] +ₗ (-ₗ [ a ])) ≡ 0ₗ
  +ₗ-rinv[] (r , s , s∈S) = eq/ _ _ ((1r , SMultClosedSubset .containsOne) , path)
   where
   path : 1r · (r · s + - r · s) · 1r ≡ 1r · 0r · (s · s)
   path = 1r · (r · s + - r · s) · 1r   ≡⟨ cong (λ x → 1r · (r · s + x) · 1r) (-commutesWithLeft-· _ _) ⟩
          1r · (r · s + - (r · s)) · 1r ≡⟨ cong (λ x → 1r · x · 1r) (+-rinv _) ⟩
          1r · 0r · 1r                  ≡⟨ ·-rid _ ⟩
          1r · 0r                       ≡⟨ ·-lid _ ⟩
          0r                            ≡⟨ sym (0-leftNullifies _) ⟩
          0r · (s · s)                  ≡⟨ cong (_· (s · s)) (sym (·-lid _)) ⟩
          1r · 0r · (s · s)             ∎


 +ₗ-comm : (x y : S⁻¹R) → x +ₗ y ≡ y +ₗ x
 +ₗ-comm = SQ.elimProp2 (λ _ _ → squash/ _ _) +ₗ-comm[]
  where
  +ₗ-comm[] : (a b : R × S) → ([ a ] +ₗ [ b ]) ≡ ([ b ] +ₗ [ a ])
  +ₗ-comm[] (r , s , s∈S) (r' , s' , s'∈S) =
            cong [_] (ΣPathP ((+-comm _ _) , Σ≡Prop (λ x → ∈-isProp S' x) (·-comm _ _)))


 -- Now for multiplication
 _·ₗ_ : S⁻¹R → S⁻¹R → S⁻¹R
 _·ₗ_ = setQuotBinOp locRefl _·ₚ_ θ
  where
  _·ₚ_ : R × S → R × S → R × S
  (r₁ , s₁ , s₁∈S) ·ₚ (r₂ , s₂ , s₂∈S) =
                      (r₁ · r₂) , ((s₁ · s₂) , SMultClosedSubset .multClosed s₁∈S s₂∈S)

  θ : (a a' b b' : R × S) → a ≈ a' → b ≈ b' → (a ·ₚ b) ≈ (a' ·ₚ b')
  θ (r₁ , s₁ , s₁∈S) (r'₁ , s'₁ , s'₁∈S) (r₂ , s₂ , s₂∈S) (r'₂ , s'₂ , s'₂∈S) (s , p) (s' , q) =
    ((fst s · fst s') , SMultClosedSubset .multClosed (s .snd) (s' .snd)) , path
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
 1ₗ : S⁻¹R
 1ₗ = [ 1r , 1r , SMultClosedSubset .containsOne ]

 ·ₗ-assoc : (x y z : S⁻¹R) → x ·ₗ (y ·ₗ z) ≡ (x ·ₗ y) ·ₗ z
 ·ₗ-assoc = SQ.elimProp3 (λ _ _ _ → squash/ _ _) ·ₗ-assoc[]
   where
   ·ₗ-assoc[] : (a b c : R × S) → [ a ] ·ₗ ([ b ] ·ₗ [ c ]) ≡ ([ a ] ·ₗ [ b ]) ·ₗ [ c ]
   ·ₗ-assoc[] (r , s , s∈S) (r' , s' , s'∈S) (r'' , s'' , s''∈S) =
              cong [_] (ΣPathP ((·-assoc _ _ _) , Σ≡Prop (λ x → ∈-isProp S' x) (·-assoc _ _ _)))

 ·ₗ-rid : (x : S⁻¹R) → x ·ₗ 1ₗ ≡ x
 ·ₗ-rid = SQ.elimProp (λ _ → squash/ _ _) ·ₗ-rid[]
   where
   ·ₗ-rid[] : (a : R × S) → ([ a ] ·ₗ 1ₗ) ≡ [ a ]
   ·ₗ-rid[] (r , s , s∈S) = cong [_] (ΣPathP ((·-rid _) , Σ≡Prop (λ x → ∈-isProp S' x) (·-rid _)))


 ·ₗ-rdist-+ₗ : (x y z : S⁻¹R) → x ·ₗ (y +ₗ z) ≡ (x ·ₗ y) +ₗ (x ·ₗ z)
 ·ₗ-rdist-+ₗ = SQ.elimProp3 (λ _ _ _ → squash/ _ _) ·ₗ-rdist-+ₗ[]
   where
   ·ₗ-rdist-+ₗ[] : (a b c : R × S) → [ a ] ·ₗ ([ b ] +ₗ [ c ]) ≡ ([ a ] ·ₗ [ b ]) +ₗ ([ a ] ·ₗ [ c ])
   ·ₗ-rdist-+ₗ[] (r , s , s∈S) (r' , s' , s'∈S) (r'' , s'' , s''∈S) =
      eq/ _ _ ((1r , (SMultClosedSubset .containsOne)) , path)
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


 ·ₗ-comm : (x y : S⁻¹R) → x ·ₗ y ≡ y ·ₗ x
 ·ₗ-comm = SQ.elimProp2 (λ _ _ → squash/ _ _) ·ₗ-comm[]
   where
   ·ₗ-comm[] : (a b : R × S) → [ a ] ·ₗ [ b ] ≡ [ b ] ·ₗ [ a ]
   ·ₗ-comm[] (r , s , s∈S) (r' , s' , s'∈S) =
             cong [_] (ΣPathP ((·-comm _ _) , Σ≡Prop (λ x → ∈-isProp S' x) (·-comm _ _)))



 -- Commutative ring structure on S⁻¹R
 S⁻¹RAsCommRing : CommRing
 S⁻¹RAsCommRing = S⁻¹R , S⁻¹RCommRingStr
  where
  open CommRingStr
  S⁻¹RCommRingStr : CommRingStr S⁻¹R
  0r S⁻¹RCommRingStr = 0ₗ
  1r S⁻¹RCommRingStr = 1ₗ
  _+_ S⁻¹RCommRingStr = _+ₗ_
  _·_ S⁻¹RCommRingStr = _·ₗ_
  - S⁻¹RCommRingStr = -ₗ_
  isCommRing S⁻¹RCommRingStr = makeIsCommRing squash/ +ₗ-assoc +ₗ-rid +ₗ-rinv +ₗ-comm
                                                      ·ₗ-assoc ·ₗ-rid ·ₗ-rdist-+ₗ ·ₗ-comm

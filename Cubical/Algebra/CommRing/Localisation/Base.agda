-- We define the localisation of a commutative ring
-- at a multiplicatively closed subset and show that it
-- has a commutative ring structure.

{-# OPTIONS --safe --lossy-unification #-}
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
open import Cubical.Data.Nat renaming ( _+_ to _+ℕ_ ; _·_ to _·ℕ_ ; _^_ to _^ℕ_
                                      ; +-comm to +ℕ-comm ; +-assoc to +ℕ-assoc
                                      ; ·-assoc to ·ℕ-assoc ; ·-comm to ·ℕ-comm)
open import Cubical.Data.Vec
open import Cubical.Data.Sigma.Base
open import Cubical.Data.Sigma.Properties
open import Cubical.Data.FinData
open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary

open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Tactics.CommRingSolver

open import Cubical.HITs.SetQuotients as SQ
open import Cubical.HITs.PropositionalTruncation as PT

open Iso

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ


-- A multiplicatively closed subset is assumed to contain 1
record isMultClosedSubset (R' : CommRing ℓ) (S' : ℙ (fst R')) : Type ℓ where
 constructor
   multclosedsubset
 field
   containsOne : (R' .snd .CommRingStr.1r) ∈ S'
   multClosed : ∀ {s t} → s ∈ S' → t ∈ S' → ((snd R') .CommRingStr._·_ s t) ∈ S'

module Loc (R' : CommRing ℓ) (S' : ℙ (fst R')) (SMultClosedSubset : isMultClosedSubset R' S') where
 open isMultClosedSubset
 private R = fst R'
 open CommRingStr (snd R')
 open RingTheory (CommRing→Ring R')
 open CommRingTheory R'

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
  path = u · v · s' · r · s''   ≡⟨ solve! R' ⟩
         u · r · s' · v · s''   ≡⟨ cong (λ x → x · v · s'') p ⟩
         u · r' · s · v · s''   ≡⟨ solve! R' ⟩
         u · s · (v · r' · s'') ≡⟨ cong (u · s ·_) q ⟩
         u · s · (v · r'' · s') ≡⟨ solve! R' ⟩
         u · v · s' · r'' · s   ∎

 locIsEquivRel : isEquivRel _≈_
 isEquivRel.reflexive locIsEquivRel = locRefl
 isEquivRel.symmetric locIsEquivRel = locSym
 isEquivRel.transitive locIsEquivRel = locTrans

 _+ₗ_ : S⁻¹R → S⁻¹R → S⁻¹R
 _+ₗ_ = setQuotSymmBinOp locRefl locTrans _+ₚ_
         (λ a b → subst (λ x → (a +ₚ b) ≈ x) (+ₚ-symm a b) (locRefl (a +ₚ b))) θ
  where
  _+ₚ_ : R × S → R × S → R × S
  (r₁ , s₁ , s₁∈S) +ₚ (r₂ , s₂ , s₂∈S) =
                      (r₁ · s₂ + r₂ · s₁) , (s₁ · s₂) , SMultClosedSubset .multClosed s₁∈S s₂∈S

  +ₚ-symm : (a b : R × S) → (a +ₚ b) ≡ (b +ₚ a)
  +ₚ-symm (r₁ , s₁ , s₁∈S) (r₂ , s₂ , s₂∈S) =
          ΣPathP (+Comm _ _ , Σ≡Prop (λ x → S' x .snd) (·Comm _ _))

  θ : (a a' b : R × S) → a ≈ a' → (a +ₚ b) ≈ (a' +ₚ b)
  θ (r₁ , s₁ , s₁∈S) (r'₁ , s'₁ , s'₁∈S) (r₂ , s₂ , s₂∈S) ((s , s∈S) , p) = (s , s∈S) , path
    where

    path : s · (r₁ · s₂ + r₂ · s₁) · (s'₁ · s₂) ≡ s · (r'₁ · s₂ + r₂ · s'₁) · (s₁ · s₂)
    path = s · (r₁ · s₂ + r₂ · s₁) · (s'₁ · s₂)

         ≡⟨ solve! R' ⟩

           s · r₁ · s'₁ · s₂ · s₂ + s · r₂ · s₁ · s'₁ · s₂

         ≡⟨ cong (λ x → x · s₂ · s₂ + s · r₂ · s₁ · s'₁ · s₂) p ⟩

           s · r'₁ · s₁ · s₂ · s₂ + s · r₂ · s₁ · s'₁ · s₂

         ≡⟨ solve! R' ⟩

           s · (r'₁ · s₂ + r₂ · s'₁) · (s₁ · s₂) ∎


 -- check group-laws for addition
 +ₗ-assoc : (x y z : S⁻¹R) → x +ₗ (y +ₗ z) ≡ (x +ₗ y) +ₗ z
 +ₗ-assoc = SQ.elimProp3 (λ _ _ _ → squash/ _ _) +ₗ-assoc[]
  where
  +ₗ-assoc[] : (a b c : R × S) → [ a ] +ₗ ([ b ] +ₗ [ c ]) ≡ ([ a ] +ₗ [ b ]) +ₗ [ c ]
  +ₗ-assoc[] (r , s , s∈S) (r' , s' , s'∈S) (r'' , s'' , s''∈S) =
     cong [_] (ΣPathP ((solve! R') , Σ≡Prop (λ x → ∈-isProp S' x) (·Assoc _ _ _)))

 0ₗ : S⁻¹R
 0ₗ = [ 0r , 1r , SMultClosedSubset .containsOne ]

 +ₗ-rid : (x : S⁻¹R) → x +ₗ 0ₗ ≡ x
 +ₗ-rid = SQ.elimProp (λ _ → squash/ _ _) +ₗ-rid[]
  where
  +ₗ-rid[] : (a : R × S) → [ a ] +ₗ 0ₗ ≡ [ a ]
  +ₗ-rid[] (r , s , s∈S) = path
   where
   path : [ r · 1r + 0r · s , s · 1r , SMultClosedSubset .multClosed s∈S
                                      (SMultClosedSubset .containsOne) ]
        ≡ [ r , s , s∈S ]
   path = cong [_] (ΣPathP (solve! R' , Σ≡Prop (λ x → ∈-isProp S' x) (·IdR _)))

 -ₗ_ : S⁻¹R → S⁻¹R
 -ₗ_ = SQ.rec squash/ -ₗ[] -ₗWellDef
  where
  -ₗ[] : R × S → S⁻¹R
  -ₗ[] (r , s) = [ - r , s ]

  -ₗWellDef : (a b : R × S) → a ≈ b → -ₗ[] a ≡ -ₗ[] b
  -ₗWellDef (r , s , _) (r' , s' , _) ((u , u∈S) , p) = eq/ _ _ ((u , u∈S) , path)
   where
   path : u · - r · s' ≡ u · - r' · s
   path = (solve! R') ∙∙ cong -_ p ∙∙ (solve! R')

 +ₗ-rinv : (x : S⁻¹R) → x +ₗ (-ₗ x) ≡ 0ₗ
 +ₗ-rinv = SQ.elimProp (λ _ → squash/ _ _) +ₗ-rinv[]
  where
  +ₗ-rinv[] : (a : R × S) → ([ a ] +ₗ (-ₗ [ a ])) ≡ 0ₗ
  +ₗ-rinv[] (r , s , s∈S) = eq/ _ _ ((1r , SMultClosedSubset .containsOne) , solve! R')

 +ₗ-comm : (x y : S⁻¹R) → x +ₗ y ≡ y +ₗ x
 +ₗ-comm = SQ.elimProp2 (λ _ _ → squash/ _ _) +ₗ-comm[]
  where
  +ₗ-comm[] : (a b : R × S) → ([ a ] +ₗ [ b ]) ≡ ([ b ] +ₗ [ a ])
  +ₗ-comm[] (r , s , s∈S) (r' , s' , s'∈S) =
            cong [_] (ΣPathP ((+Comm _ _) , Σ≡Prop (λ x → ∈-isProp S' x) (·Comm _ _)))


 -- Now for multiplication
 _·ₗ_ : S⁻¹R → S⁻¹R → S⁻¹R
 _·ₗ_ = setQuotSymmBinOp locRefl locTrans _·ₚ_
         (λ a b → subst (λ x → (a ·ₚ b) ≈ x) (·ₚ-symm a b) (locRefl (a ·ₚ b))) θ
  where
  _·ₚ_ : R × S → R × S → R × S
  (r₁ , s₁ , s₁∈S) ·ₚ (r₂ , s₂ , s₂∈S) =
                      (r₁ · r₂) , ((s₁ · s₂) , SMultClosedSubset .multClosed s₁∈S s₂∈S)

  ·ₚ-symm : (a b : R × S) → (a ·ₚ b) ≡ (b ·ₚ a)
  ·ₚ-symm (r₁ , s₁ , s₁∈S) (r₂ , s₂ , s₂∈S) =
          ΣPathP (·Comm _ _ , Σ≡Prop (λ x → S' x .snd) (·Comm _ _))

  θ : (a a' b : R × S) → a ≈ a' → (a ·ₚ b) ≈ (a' ·ₚ b)
  θ (r₁ , s₁ , s₁∈S) (r'₁ , s'₁ , s'₁∈S) (r₂ , s₂ , s₂∈S) ((s , s∈S) , p) = (s , s∈S) , path
   where
   path : s · (r₁ · r₂) · (s'₁ · s₂) ≡ s · (r'₁ · r₂) · (s₁ · s₂)
   path = solve! R' ∙∙ cong (λ x → x · r₂ · s₂) p ∙∙ solve! R'


 -- checking laws for multiplication
 1ₗ : S⁻¹R
 1ₗ = [ 1r , 1r , SMultClosedSubset .containsOne ]

 ·ₗ-assoc : (x y z : S⁻¹R) → x ·ₗ (y ·ₗ z) ≡ (x ·ₗ y) ·ₗ z
 ·ₗ-assoc = SQ.elimProp3 (λ _ _ _ → squash/ _ _) ·ₗ-assoc[]
   where
   ·ₗ-assoc[] : (a b c : R × S) → [ a ] ·ₗ ([ b ] ·ₗ [ c ]) ≡ ([ a ] ·ₗ [ b ]) ·ₗ [ c ]
   ·ₗ-assoc[] (r , s , s∈S) (r' , s' , s'∈S) (r'' , s'' , s''∈S) =
              cong [_] (ΣPathP ((·Assoc _ _ _) , Σ≡Prop (λ x → ∈-isProp S' x) (·Assoc _ _ _)))

 ·ₗ-rid : (x : S⁻¹R) → x ·ₗ 1ₗ ≡ x
 ·ₗ-rid = SQ.elimProp (λ _ → squash/ _ _) ·ₗ-rid[]
   where
   ·ₗ-rid[] : (a : R × S) → ([ a ] ·ₗ 1ₗ) ≡ [ a ]
   ·ₗ-rid[] (r , s , s∈S) = cong [_] (ΣPathP ((·IdR _) , Σ≡Prop (λ x → ∈-isProp S' x) (·IdR _)))


 ·ₗ-rdist-+ₗ : (x y z : S⁻¹R) → x ·ₗ (y +ₗ z) ≡ (x ·ₗ y) +ₗ (x ·ₗ z)
 ·ₗ-rdist-+ₗ = SQ.elimProp3 (λ _ _ _ → squash/ _ _) ·ₗ-rdist-+ₗ[]
   where
   ·ₗ-rdist-+ₗ[] : (a b c : R × S) → [ a ] ·ₗ ([ b ] +ₗ [ c ]) ≡ ([ a ] ·ₗ [ b ]) +ₗ ([ a ] ·ₗ [ c ])
   ·ₗ-rdist-+ₗ[] (r , s , s∈S) (r' , s' , s'∈S) (r'' , s'' , s''∈S) =
      eq/ _ _ ((1r , (SMultClosedSubset .containsOne)) , solve! R')

 ·ₗ-comm : (x y : S⁻¹R) → x ·ₗ y ≡ y ·ₗ x
 ·ₗ-comm = SQ.elimProp2 (λ _ _ → squash/ _ _) ·ₗ-comm[]
   where
   ·ₗ-comm[] : (a b : R × S) → [ a ] ·ₗ [ b ] ≡ [ b ] ·ₗ [ a ]
   ·ₗ-comm[] (r , s , s∈S) (r' , s' , s'∈S) =
             cong [_] (ΣPathP ((·Comm _ _) , Σ≡Prop (λ x → ∈-isProp S' x) (·Comm _ _)))



 -- Commutative ring structure on S⁻¹R
 S⁻¹RAsCommRing : CommRing ℓ
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

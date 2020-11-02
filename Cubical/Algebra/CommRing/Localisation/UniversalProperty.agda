-- We define what it means to satisfy the universal property
-- of localisation and show that the localisation in Base satisfies
-- it. We will also show that the localisation is uniquely determined
-- by the universal property, and give sufficient criteria for
-- satisfying the universal property.

{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.CommRing.Localisation.UniversalProperty where

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
open import Cubical.Algebra.CommRing.Localisation.Base

open import Cubical.HITs.SetQuotients as SQ
open import Cubical.HITs.PropositionalTruncation as PT

open Iso

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ

module _ (R' : CommRing {ℓ}) (S' : ℙ (R' .fst)) (SMultClosedSubset : isMultClosedSubset R' S') where
 open isMultClosedSubset
 private R = R' .fst
 open CommRingStr (R' .snd) hiding (is-set)
 open Theory (CommRing→Ring R')
 open RingHom



 hasLocUniversalProp : (A : CommRing {ℓ}) (φ : CommRingHom R' A)
                     → (∀ s → s ∈ S' → f φ s ∈ A ˣ)
                     → Type (ℓ-suc ℓ)
 hasLocUniversalProp A φ _ = (B : CommRing {ℓ}) (ψ : CommRingHom R' B)
                           → (∀ s → s ∈ S' → f ψ s ∈ B ˣ)
                           → ∃![ χ ∈ CommRingHom A B ] (f χ) ∘ (f φ) ≡ (f ψ)

 UniversalPropIsProp : (A : CommRing {ℓ}) (φ : CommRingHom R' A)
                     → (φS⊆Aˣ : ∀ s → s ∈ S' → f φ s ∈ A ˣ)
                     → isProp (hasLocUniversalProp A φ φS⊆Aˣ)
 UniversalPropIsProp A φ φS⊆Aˣ = isPropΠ3 (λ _ _ _ → isPropIsContr)

 -- S⁻¹R has the universal property
 module S⁻¹RUniversalProp where
 open Loc R' S' SMultClosedSubset
 _/1 : R → S⁻¹R
 r /1 = [ r , 1r , SMultClosedSubset .containsOne ]

 /1AsCommRingHom : CommRingHom R' S⁻¹RAsCommRing
 f /1AsCommRingHom = _/1
 pres1 /1AsCommRingHom = refl
 isHom+ /1AsCommRingHom r r' = cong [_] (≡-× (cong₂ (_+_) (sym (·-rid r)) (sym (·-rid r')))
                                        (Σ≡Prop (λ x → S' x .snd) (sym (·-lid 1r))))
 isHom· /1AsCommRingHom r r' = cong [_] (≡-× refl (Σ≡Prop (λ x → S' x .snd) (sym (·-lid 1r))))

 S⁻¹Rˣ = S⁻¹RAsCommRing ˣ
 S/1⊆S⁻¹Rˣ : ∀ s → s ∈ S' → (s /1) ∈ S⁻¹Rˣ
 S/1⊆S⁻¹Rˣ s s∈S' = [ 1r , s , s∈S' ] , eq/ _ _ ((1r , SMultClosedSubset .containsOne) , path)
  where
  path : 1r · (s · 1r) · 1r ≡ 1r · 1r · (1r  · s)
  path = 1r · (s · 1r) · 1r ≡⟨ (λ i → ·-rid (·-lid (·-rid s i) i) i) ⟩
         s                  ≡⟨ (λ i → ·-lid (·-lid s (~ i)) (~ i)) ⟩
         1r · (1r  · s)     ≡⟨ cong (_· (1r · s)) (sym (·-lid _)) ⟩
         1r · 1r · (1r  · s) ∎

 S⁻¹RHasUniversalProp : hasLocUniversalProp S⁻¹RAsCommRing /1AsCommRingHom S/1⊆S⁻¹Rˣ
 S⁻¹RHasUniversalProp B' ψ ψS⊆Bˣ = (χ , funExt χcomp) , χunique
  where
  B = B' .fst
  open CommRingStr (B' .snd) renaming ( is-set to Bset ; _·_ to _·B_ ; 1r to 1b
                                      ; _+_ to _+B_
                                      ; ·-assoc to ·B-assoc ; ·-comm to ·B-comm
                                      ; ·-lid to ·B-lid ; ·-rid to ·B-rid)
  open Units B' renaming (Rˣ to Bˣ ; RˣMultClosed to BˣMultClosed ; RˣContainsOne to BˣContainsOne)
  open CommTheory B'

  χ : CommRingHom S⁻¹RAsCommRing B'
  f χ = SQ.rec Bset fχ fχcoh
   where
   fχ : R × S → B
   fχ (r , s , s∈S') = (f ψ r) ·B ((f ψ s) ⁻¹) ⦃ ψS⊆Bˣ s s∈S' ⦄
   fχcoh : (a b : R × S) → a ≈ b → fχ a ≡ fχ b
   fχcoh (r , s , s∈S') (r' , s' , s'∈S') (u , p) = instancepath ⦃ ψS⊆Bˣ s s∈S' ⦄ ⦃ ψS⊆Bˣ s' s'∈S' ⦄
    where
    instancepath : ⦃ _ : f ψ s ∈ Bˣ ⦄ ⦃ _ : f ψ s' ∈ Bˣ ⦄
                 → (f ψ r) ·B ((f ψ s) ⁻¹) ≡ (f ψ r') ·B ((f ψ s') ⁻¹)
    instancepath = (f ψ r) ·B ((f ψ s) ⁻¹)   ≡⟨ {!!} ⟩
                   (f ψ r') ·B ((f ψ s') ⁻¹) ∎

  pres1 χ = instancepres1χ ⦃ ψS⊆Bˣ 1r (SMultClosedSubset .containsOne) ⦄ ⦃ BˣContainsOne ⦄
   where
   instancepres1χ : ⦃ _ : f ψ 1r ∈ Bˣ ⦄ ⦃ _ : 1b ∈ Bˣ ⦄
                  → f ψ 1r ·B (f ψ 1r) ⁻¹ ≡ 1b
   instancepres1χ =  (λ i → (pres1 ψ i) ·B (unitCong (pres1 ψ) i))
                   ∙ (λ i → ·B-lid (1⁻¹≡1 i) i)

  isHom+ χ = elimProp2 (λ _ _ _ _ → Bset _ _ _ _) isHom+[]
   where
   isHom+[] : (a b : R × S) → f χ ([ a ] +ₗ [ b ]) ≡ (f χ [ a ]) +B (f χ [ b ])
   isHom+[] (r , s , s∈S') (r' , s' , s'∈S') = instancepath
    ⦃ ψS⊆Bˣ s s∈S' ⦄ ⦃ ψS⊆Bˣ s' s'∈S' ⦄ ⦃ ψS⊆Bˣ (s · s') (SMultClosedSubset .multClosed s∈S' s'∈S') ⦄
    ⦃ BˣMultClosed _ _ ⦃ ψS⊆Bˣ s s∈S' ⦄ ⦃ ψS⊆Bˣ s' s'∈S' ⦄ ⦄
    where
    instancepath : ⦃ _ : f ψ s ∈ Bˣ ⦄ ⦃ _ : f ψ s' ∈ Bˣ ⦄
                   ⦃ _ : f ψ (s · s') ∈ Bˣ ⦄ ⦃ _ : f ψ s ·B f ψ s' ∈ Bˣ ⦄
               → f ψ (r · s' + r' · s) ·B f ψ (s · s') ⁻¹ ≡ f ψ r ·B f ψ s ⁻¹ +B f ψ r' ·B f ψ s' ⁻¹
    instancepath = {!!}

  isHom· χ = elimProp2 (λ _ _ _ _ → Bset _ _ _ _) isHom·[]
   where
   isHom·[] : (a b : R × S) → f χ ([ a ] ·ₗ [ b ]) ≡ (f χ [ a ]) ·B (f χ [ b ])
   isHom·[] (r , s , s∈S') (r' , s' , s'∈S') = instancepath
    ⦃ ψS⊆Bˣ s s∈S' ⦄ ⦃ ψS⊆Bˣ s' s'∈S' ⦄ ⦃ ψS⊆Bˣ (s · s') (SMultClosedSubset .multClosed s∈S' s'∈S') ⦄
    ⦃ BˣMultClosed _ _ ⦃ ψS⊆Bˣ s s∈S' ⦄ ⦃ ψS⊆Bˣ s' s'∈S' ⦄ ⦄
    where
    instancepath : ⦃ _ : f ψ s ∈ Bˣ ⦄ ⦃ _ : f ψ s' ∈ Bˣ ⦄
                   ⦃ _ : f ψ (s · s') ∈ Bˣ ⦄ ⦃ _ : f ψ s ·B f ψ s' ∈ Bˣ ⦄
                 → f ψ (r · r') ·B f ψ (s · s') ⁻¹ ≡ (f ψ r ·B f ψ s ⁻¹) ·B (f ψ r' ·B f ψ s' ⁻¹)
    instancepath = f ψ (r · r') ·B f ψ (s · s') ⁻¹
                 ≡⟨ (λ i → isHom· ψ r r' i ·B unitCong (isHom· ψ s s') i) ⟩
                   f ψ r ·B f ψ r' ·B (f ψ s ·B f ψ s') ⁻¹
                 ≡⟨ cong (f ψ r ·B f ψ r' ·B_) (⁻¹-dist-· _ _) ⟩
                   f ψ r ·B f ψ r' ·B (f ψ s ⁻¹ ·B f ψ s' ⁻¹)
                 ≡⟨ ·-commAssocSwap _ _ _ _ ⟩
                   f ψ r ·B f ψ s ⁻¹ ·B (f ψ r' ·B f ψ s' ⁻¹) ∎


  χcomp : (r : R) → f χ (r /1) ≡ f ψ r
  χcomp = instanceχcomp ⦃ ψS⊆Bˣ 1r (SMultClosedSubset .containsOne) ⦄ ⦃ Units.RˣContainsOne B' ⦄
   where
   instanceχcomp : ⦃ _ : f ψ 1r ∈ Bˣ ⦄ ⦃ _ : 1b ∈ Bˣ ⦄
                   (r : R) → f ψ r ·B (f ψ 1r) ⁻¹ ≡ f ψ r
   instanceχcomp r = f ψ r ·B (f ψ 1r) ⁻¹ ≡⟨ cong (f ψ r ·B_) (unitCong (pres1 ψ)) ⟩
                     f ψ r ·B 1b ⁻¹       ≡⟨ cong (f ψ r ·B_) 1⁻¹≡1 ⟩
                     f ψ r ·B 1b          ≡⟨ ·B-rid _ ⟩
                     f ψ r ∎


  χunique : (y : Σ[ χ' ∈ CommRingHom S⁻¹RAsCommRing B' ] f χ' ∘ _/1 ≡ f ψ)
          → (χ , funExt χcomp) ≡ y
  χunique (χ' , χ'/1≡ψ) = Σ≡Prop (λ x → isSetΠ (λ _ → Bset) _ _) {!!}
   where
   open RingHomRespUnits {A' = S⁻¹RAsCommRing} {B' = B'} χ'
                         renaming (φ[x⁻¹]≡φ[x]⁻¹ to χ'[x⁻¹]≡χ'[x]⁻¹)

   []-path : (a : R × S) → f χ [ a ] ≡ f χ' [ a ]
   []-path (r , s , s∈S') = instancepath ⦃ ψS⊆Bˣ s s∈S' ⦄ ⦃ S/1⊆S⁻¹Rˣ s s∈S' ⦄
                                         ⦃ RingHomRespInv _ ⦃ S/1⊆S⁻¹Rˣ s s∈S' ⦄ ⦄
    where
    open Units S⁻¹RAsCommRing renaming (_⁻¹ to _⁻¹ˡ ; inverseUniqueness to S⁻¹RInverseUniqueness)
                              hiding (unitCong)

    s-inv : ⦃ s/1∈S⁻¹Rˣ : s /1 ∈ S⁻¹Rˣ ⦄ → s /1 ⁻¹ˡ ≡ [ 1r , s , s∈S' ]
    s-inv ⦃ s/1∈S⁻¹Rˣ ⦄ = PathPΣ (S⁻¹RInverseUniqueness (s /1) s/1∈S⁻¹Rˣ (_ , eq/ _ _ ((1r , SMultClosedSubset .containsOne) , {!!}))) .fst

    ·ₗ-path : [ r , s , s∈S' ] ≡   [ r , 1r , SMultClosedSubset .containsOne ]
                                ·ₗ [ 1r , s , s∈S' ]
    ·ₗ-path = cong [_] (≡-× (sym (·-rid r)) (Σ≡Prop (λ x → S' x .snd) (sym (·-lid s))))

    instancepath : ⦃ _ : f ψ s ∈ Bˣ ⦄ ⦃ _ : s /1 ∈ S⁻¹Rˣ ⦄ ⦃ _ : f χ' (s /1) ∈ Bˣ ⦄
                 → f ψ r ·B f ψ s ⁻¹ ≡ f χ' [ r , s , s∈S' ]
    instancepath = f ψ r ·B f ψ s ⁻¹
                 ≡⟨ cong (f ψ r ·B_) (unitCong (cong (λ φ → φ s) (sym χ'/1≡ψ))) ⟩
                   f ψ r ·B f χ' (s /1) ⁻¹
                 ≡⟨ cong (f ψ r ·B_) (sym (χ'[x⁻¹]≡χ'[x]⁻¹ _)) ⟩
                   f ψ r ·B f χ' (s /1 ⁻¹ˡ)
                 ≡⟨ cong (λ x → f ψ r ·B f χ' x) s-inv ⟩
                   f ψ r ·B f χ' [ 1r , s , s∈S' ]
                 ≡⟨ cong (_·B f χ' [ 1r , s , s∈S' ]) (cong (λ φ → φ r) (sym χ'/1≡ψ)) ⟩
                   f χ' [ r , 1r , SMultClosedSubset .containsOne ] ·B f χ' [ 1r , s , s∈S' ]
                 ≡⟨ sym (isHom· χ' _ _) ⟩
                   f χ' ([ r , 1r , SMultClosedSubset .containsOne ] ·ₗ [ 1r , s , s∈S' ])
                 ≡⟨ cong (f χ') (sym ·ₗ-path) ⟩
                   f χ' [ r , s , s∈S' ] ∎

   fχ≡fχ' : f χ ≡ f χ'
   fχ≡fχ' = funExt (SQ.elimProp (λ _ → Bset _ _) []-path)

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
open import Cubical.Functions.Surjection
open import Cubical.Functions.Embedding

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
open import Cubical.Algebra.RingSolver.ReflectionSolving
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Localisation.Base

open import Cubical.HITs.SetQuotients as SQ
open import Cubical.HITs.PropositionalTruncation as PT

open Iso

private
  variable
    ℓ ℓ' : Level


module _ (R' : CommRing {ℓ}) (S' : ℙ (fst R')) (SMultClosedSubset : isMultClosedSubset R' S') where
 open isMultClosedSubset
 private R = fst R'
 open CommRingStr (snd R') hiding (is-set)
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
  isHom+ /1AsCommRingHom r r' = cong [_] (≡-× (cong₂ (_+_) (sym (·Rid r)) (sym (·Rid r')))
                                         (Σ≡Prop (λ x → S' x .snd) (sym (·Lid 1r))))
  isHom· /1AsCommRingHom r r' = cong [_] (≡-× refl (Σ≡Prop (λ x → S' x .snd) (sym (·Lid 1r))))

  S⁻¹Rˣ = S⁻¹RAsCommRing ˣ
  S/1⊆S⁻¹Rˣ : ∀ s → s ∈ S' → (s /1) ∈ S⁻¹Rˣ
  S/1⊆S⁻¹Rˣ s s∈S' = [ 1r , s , s∈S' ] , eq/ _ _ ((1r , SMultClosedSubset .containsOne) , path s)
   where
   path : ∀ s → 1r · (s · 1r) · 1r ≡ 1r · 1r · (1r  · s)
   path = solve R'

  S⁻¹RHasUniversalProp : hasLocUniversalProp S⁻¹RAsCommRing /1AsCommRingHom S/1⊆S⁻¹Rˣ
  S⁻¹RHasUniversalProp B' ψ ψS⊆Bˣ = (χ , funExt χcomp) , χunique
   where
   B = fst B'
   open CommRingStr (snd B') renaming  ( is-set to Bset ; _·_ to _·B_ ; 1r to 1b
                                       ; _+_ to _+B_
                                       ; ·Assoc to ·B-assoc ; ·-comm to ·B-comm
                                       ; ·Lid to ·B-lid ; ·Rid to ·B-rid
                                       ; ·Ldist+ to ·B-ldist-+)
   open Units B' renaming (Rˣ to Bˣ ; RˣMultClosed to BˣMultClosed ; RˣContainsOne to BˣContainsOne)
   open Theory (CommRing→Ring B') renaming (·-assoc2 to ·B-assoc2)
   open CommTheory B' renaming (·-commAssocl to ·B-commAssocl ; ·-commAssocSwap to ·B-commAssocSwap)

   χ : CommRingHom S⁻¹RAsCommRing B'
   f χ = SQ.rec Bset fχ fχcoh
    where
    fχ : R × S → B
    fχ (r , s , s∈S') = (f ψ r) ·B ((f ψ s) ⁻¹) ⦃ ψS⊆Bˣ s s∈S' ⦄
    fχcoh : (a b : R × S) → a ≈ b → fχ a ≡ fχ b
    fχcoh (r , s , s∈S') (r' , s' , s'∈S') ((u , u∈S') , p) = instancepath
     ⦃ ψS⊆Bˣ s s∈S' ⦄ ⦃ ψS⊆Bˣ s' s'∈S' ⦄ ⦃ ψS⊆Bˣ (u · s · s')
            (SMultClosedSubset .multClosed (SMultClosedSubset .multClosed u∈S' s∈S') s'∈S') ⦄
     ⦃ BˣMultClosed _ _ ⦃ ψS⊆Bˣ (u · s) (SMultClosedSubset .multClosed u∈S' s∈S') ⦄
                        ⦃ ψS⊆Bˣ s' s'∈S' ⦄ ⦄
     ⦃ ψS⊆Bˣ (u · s) (SMultClosedSubset .multClosed u∈S' s∈S') ⦄
     where
     -- only a few indidividual steps can be solved by the ring solver yet
     instancepath : ⦃ _ : f ψ s ∈ Bˣ ⦄ ⦃ _ : f ψ s' ∈ Bˣ ⦄
                    ⦃ _ : f ψ (u · s · s') ∈ Bˣ ⦄ ⦃ _ : f ψ (u · s) ·B f ψ s' ∈ Bˣ ⦄
                    ⦃ _ : f ψ (u · s) ∈ Bˣ ⦄
                  → f ψ r ·B f ψ s ⁻¹ ≡ f ψ r' ·B f ψ s' ⁻¹
     instancepath = f ψ r ·B f ψ s ⁻¹

                  ≡⟨ sym (·B-rid _) ⟩

                    f ψ r ·B f ψ s ⁻¹ ·B 1b

                  ≡⟨ cong (f ψ r ·B f ψ s ⁻¹ ·B_) (sym (·-rinv _)) ⟩

                    f ψ r ·B f ψ s ⁻¹ ·B (f ψ (u · s · s') ·B f ψ (u · s · s') ⁻¹)

                  ≡⟨ ·B-assoc _ _ _ ⟩

                    f ψ r ·B f ψ s ⁻¹ ·B f ψ (u · s · s') ·B f ψ (u · s · s') ⁻¹

                  ≡⟨ cong (λ x → f ψ r ·B f ψ s ⁻¹ ·B x ·B f ψ (u · s · s') ⁻¹) (isHom· ψ _ _) ⟩

                    f ψ r ·B f ψ s ⁻¹ ·B (f ψ (u · s) ·B f ψ s') ·B f ψ (u · s · s') ⁻¹

                  ≡⟨ cong (_·B f ψ (u · s · s') ⁻¹) (·B-assoc _ _ _) ⟩

                    f ψ r ·B f ψ s ⁻¹ ·B f ψ (u · s) ·B f ψ s' ·B f ψ (u · s · s') ⁻¹

                  ≡⟨ cong (λ x → f ψ r ·B f ψ s ⁻¹ ·B x ·B f ψ s' ·B f ψ (u · s · s') ⁻¹)
                          (isHom· ψ _ _) ⟩

                    f ψ r ·B f ψ s ⁻¹ ·B (f ψ u ·B f ψ s) ·B f ψ s' ·B f ψ (u · s · s') ⁻¹

                  ≡⟨ cong (λ x → x ·B f ψ s' ·B f ψ (u · s · s') ⁻¹) (·B-commAssocSwap _ _ _ _) ⟩

                    f ψ r ·B f ψ u ·B (f ψ s ⁻¹ ·B f ψ s) ·B f ψ s' ·B f ψ (u · s · s') ⁻¹

                  ≡⟨ (λ i → ·B-comm (f ψ r) (f ψ u) i ·B (·-linv (f ψ s) i)
                                                      ·B f ψ s' ·B f ψ (u · s · s') ⁻¹) ⟩

                    f ψ u ·B f ψ r ·B 1b ·B f ψ s' ·B f ψ (u · s · s') ⁻¹

                  ≡⟨ (λ i → (·B-rid (sym (isHom· ψ u r) i) i) ·B f ψ s' ·B f ψ (u · s · s') ⁻¹) ⟩

                    f ψ (u · r) ·B f ψ s' ·B f ψ (u · s · s') ⁻¹

                  ≡⟨ cong (_·B f ψ (u · s · s') ⁻¹) (sym (isHom· ψ _ _)) ⟩

                    f ψ (u · r · s') ·B f ψ (u · s · s') ⁻¹

                  ≡⟨ cong (λ x → f ψ x ·B f ψ (u · s · s') ⁻¹) p ⟩

                    f ψ (u · r' · s) ·B f ψ (u · s · s') ⁻¹

                  ≡⟨ cong (_·B f ψ (u · s · s') ⁻¹) (isHom· ψ _ _) ⟩

                    f ψ (u · r') ·B f ψ s ·B f ψ (u · s · s') ⁻¹

                  ≡⟨ cong (λ x → x ·B f ψ s ·B f ψ (u · s · s') ⁻¹) (isHom· ψ _ _) ⟩

                    f ψ u ·B f ψ r' ·B f ψ s ·B f ψ (u · s · s') ⁻¹

                  ≡⟨ cong (_·B f ψ (u · s · s') ⁻¹) (sym (·B-assoc _ _ _)) ⟩

                    f ψ u ·B (f ψ r' ·B f ψ s) ·B f ψ (u · s · s') ⁻¹

                  ≡⟨ cong (_·B f ψ (u · s · s') ⁻¹) (·B-commAssocl _ _ _) ⟩

                    f ψ r' ·B (f ψ u ·B f ψ s) ·B f ψ (u · s · s') ⁻¹

                  ≡⟨ cong (λ x → f ψ r' ·B x ·B f ψ (u · s · s') ⁻¹) (sym (isHom· ψ _ _)) ⟩

                    f ψ r' ·B f ψ (u · s) ·B f ψ (u · s · s') ⁻¹

                  ≡⟨ cong (f ψ r' ·B f ψ (u · s) ·B_) (unitCong (isHom· ψ _ _)) ⟩

                    f ψ r' ·B f ψ (u · s) ·B (f ψ (u · s) ·B f ψ s') ⁻¹

                  ≡⟨ cong (f ψ r' ·B f ψ (u · s) ·B_) (⁻¹-dist-· _ _) ⟩

                    f ψ r' ·B f ψ (u · s) ·B (f ψ (u · s) ⁻¹ ·B f ψ s' ⁻¹)

                  ≡⟨ ·B-assoc2 _ _ _ _ ⟩

                    f ψ r' ·B (f ψ (u · s) ·B f ψ (u · s) ⁻¹) ·B f ψ s' ⁻¹

                  ≡⟨ cong (λ x → f ψ r' ·B x ·B f ψ s' ⁻¹) (·-rinv _) ⟩

                    f ψ r' ·B 1b ·B f ψ s' ⁻¹

                  ≡⟨ cong (_·B f ψ s' ⁻¹) (·B-rid _) ⟩

                    f ψ r' ·B f ψ s' ⁻¹ ∎


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
     -- only a few indidividual steps can be solved by the ring solver yet
     instancepath : ⦃ _ : f ψ s ∈ Bˣ ⦄ ⦃ _ : f ψ s' ∈ Bˣ ⦄
                    ⦃ _ : f ψ (s · s') ∈ Bˣ ⦄ ⦃ _ : f ψ s ·B f ψ s' ∈ Bˣ ⦄
                → f ψ (r · s' + r' · s) ·B f ψ (s · s') ⁻¹ ≡ f ψ r ·B f ψ s ⁻¹ +B f ψ r' ·B f ψ s' ⁻¹
     instancepath =
            f ψ (r · s' + r' · s) ·B f ψ (s · s') ⁻¹

          ≡⟨ (λ i → isHom+ ψ (r · s') (r' · s) i ·B unitCong (isHom· ψ s s') i) ⟩

            (f ψ (r · s') +B f ψ (r' · s)) ·B (f ψ s ·B f ψ s') ⁻¹

          ≡⟨ (λ i → (isHom· ψ r s' i +B isHom· ψ r' s i) ·B ⁻¹-dist-· (f ψ s) (f ψ s') i) ⟩

            (f ψ r ·B f ψ s' +B f ψ r' ·B f ψ s) ·B (f ψ s ⁻¹ ·B f ψ s' ⁻¹)

          ≡⟨ ·B-ldist-+ _ _ _ ⟩

            f ψ r ·B f ψ s' ·B (f ψ s ⁻¹ ·B f ψ s' ⁻¹) +B f ψ r' ·B f ψ s ·B (f ψ s ⁻¹ ·B f ψ s' ⁻¹)

          ≡⟨ (λ i → ·B-commAssocSwap (f ψ r) (f ψ s') (f ψ s ⁻¹) (f ψ s' ⁻¹) i
                 +B ·B-assoc2 (f ψ r') (f ψ s) (f ψ s ⁻¹) (f ψ s' ⁻¹) i) ⟩

            f ψ r ·B f ψ s ⁻¹ ·B (f ψ s' ·B f ψ s' ⁻¹) +B f ψ r' ·B (f ψ s ·B f ψ s ⁻¹) ·B f ψ s' ⁻¹

          ≡⟨ (λ i → f ψ r ·B f ψ s ⁻¹ ·B (·-rinv (f ψ s') i)
                 +B f ψ r' ·B (·-rinv (f ψ s) i) ·B f ψ s' ⁻¹) ⟩

            f ψ r ·B f ψ s ⁻¹ ·B 1b +B f ψ r' ·B 1b ·B f ψ s' ⁻¹

          ≡⟨ (λ i → ·B-rid (f ψ r ·B f ψ s ⁻¹) i +B ·B-rid (f ψ r') i ·B f ψ s' ⁻¹) ⟩

            f ψ r ·B f ψ s ⁻¹ +B f ψ r' ·B f ψ s' ⁻¹ ∎


   isHom· χ = elimProp2 (λ _ _ _ _ → Bset _ _ _ _) isHom·[]
    where
    isHom·[] : (a b : R × S) → f χ ([ a ] ·ₗ [ b ]) ≡ (f χ [ a ]) ·B (f χ [ b ])
    isHom·[] (r , s , s∈S') (r' , s' , s'∈S') = instancepath
     ⦃ ψS⊆Bˣ s s∈S' ⦄ ⦃ ψS⊆Bˣ s' s'∈S' ⦄ ⦃ ψS⊆Bˣ (s · s') (SMultClosedSubset .multClosed s∈S' s'∈S') ⦄
     ⦃ BˣMultClosed _ _ ⦃ ψS⊆Bˣ s s∈S' ⦄ ⦃ ψS⊆Bˣ s' s'∈S' ⦄ ⦄
     where
     -- only a indidividual steps can be solved by the ring solver yet
     instancepath : ⦃ _ : f ψ s ∈ Bˣ ⦄ ⦃ _ : f ψ s' ∈ Bˣ ⦄
                    ⦃ _ : f ψ (s · s') ∈ Bˣ ⦄ ⦃ _ : f ψ s ·B f ψ s' ∈ Bˣ ⦄
                  → f ψ (r · r') ·B f ψ (s · s') ⁻¹ ≡ (f ψ r ·B f ψ s ⁻¹) ·B (f ψ r' ·B f ψ s' ⁻¹)
     instancepath = f ψ (r · r') ·B f ψ (s · s') ⁻¹

                  ≡⟨ (λ i → isHom· ψ r r' i ·B unitCong (isHom· ψ s s') i) ⟩

                    f ψ r ·B f ψ r' ·B (f ψ s ·B f ψ s') ⁻¹

                  ≡⟨ cong (f ψ r ·B f ψ r' ·B_) (⁻¹-dist-· _ _) ⟩

                    f ψ r ·B f ψ r' ·B (f ψ s ⁻¹ ·B f ψ s' ⁻¹)

                  ≡⟨ ·B-commAssocSwap _ _ _ _ ⟩

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
   χunique (χ' , χ'/1≡ψ) = Σ≡Prop (λ x → isSetΠ (λ _ → Bset) _ _) (RingHom≡f _ _ fχ≡fχ')
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
     s-inv ⦃ s/1∈S⁻¹Rˣ ⦄ = PathPΣ (S⁻¹RInverseUniqueness (s /1) s/1∈S⁻¹Rˣ
                           (_ , eq/ _ _ ((1r , SMultClosedSubset .containsOne) , path s))) .fst
      where
      path : ∀ s → 1r · (s · 1r) · 1r ≡ 1r · 1r · (1r · s)
      path = solve R'

     ·ₗ-path : [ r , s , s∈S' ] ≡   [ r , 1r , SMultClosedSubset .containsOne ]
                                 ·ₗ [ 1r , s , s∈S' ]
     ·ₗ-path = cong [_] (≡-× (sym (·Rid r)) (Σ≡Prop (λ x → S' x .snd) (sym (·Lid s))))

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


 -- sufficient conditions for having the universal property
 -- used as API in the leanprover-community/mathlib
 -- Corollary 3.2 in Atiyah-McDonald
 open S⁻¹RUniversalProp
 open Loc R' S' SMultClosedSubset

 record PathToS⁻¹R (A' : CommRing {ℓ}) (φ : CommRingHom R' A') : Type ℓ where
  constructor
   pathtoS⁻¹R
  open Units A' renaming (Rˣ to Aˣ)
  open CommRingStr (snd A') renaming (is-set to Aset ; 0r to 0a ; _·_ to _·A_)
  field
   φS⊆Aˣ : ∀ s → s ∈ S' → f φ s ∈ Aˣ
   kerφ⊆annS : ∀ r → f φ r ≡ 0a → ∃[ s ∈ S ] (s .fst) · r ≡ 0r
   surχ : ∀ a → ∃[ x ∈ R × S ] f φ (x .fst) ·A (f φ (x .snd .fst) ⁻¹) ⦃ φS⊆Aˣ _ (x .snd .snd) ⦄ ≡ a

 S⁻¹RChar : (A' : CommRing {ℓ}) (φ : CommRingHom R' A')
          → PathToS⁻¹R A' φ
          → S⁻¹RAsCommRing ≡ A'
 S⁻¹RChar A' φ cond = CommRingPath S⁻¹RAsCommRing A' .fst
                    (S⁻¹R≃A , record { pres1 = pres1 χ ; isHom+ = isHom+ χ ; isHom· = isHom· χ })
  where
  open CommRingStr (snd A') renaming ( is-set to Aset ; 0r to 0a ; _·_ to _·A_ ; 1r to 1a
                                      ; ·Rid to ·A-rid)
  open Units A' renaming (Rˣ to Aˣ ; RˣInvClosed to AˣInvClosed)
  open PathToS⁻¹R ⦃...⦄
  private
   A = fst A'
   instance
    _ = cond
   χ = (S⁻¹RHasUniversalProp A' φ φS⊆Aˣ .fst .fst)
   open HomTheory χ

  S⁻¹R≃A : S⁻¹R ≃ A
  S⁻¹R≃A = f χ , isEmbedding×isSurjection→isEquiv (Embχ , Surχ)
   where
   Embχ : isEmbedding (f χ)
   Embχ = injEmbedding squash/ Aset (ker≡0→inj λ {x} → kerχ≡0 x)
    where
    kerχ≡0 : (r/s : S⁻¹R) → f χ r/s ≡ 0a → r/s ≡ 0ₗ
    kerχ≡0 = SQ.elimProp (λ _ → isPropΠ λ _ → squash/ _ _) kerχ≡[]
     where
     kerχ≡[] : (a : R × S) → f χ [ a ] ≡ 0a → [ a ] ≡ 0ₗ
     kerχ≡[] (r , s , s∈S') p = PT.rec (squash/ _ _) Σhelper
                                       (kerφ⊆annS r (UnitsAreNotZeroDivisors _ _ p))
      where
      instance
       _ : f φ s ∈ Aˣ
       _ = φS⊆Aˣ s s∈S'
       _ : f φ s ⁻¹ ∈ Aˣ
       _ = AˣInvClosed _

      Σhelper : Σ[ s ∈ S ] (s .fst) · r ≡ 0r → [ r , s , s∈S' ] ≡ 0ₗ
      Σhelper ((u , u∈S') , q) = eq/ _ _ ((u , u∈S') , path)
       where
       path : u · r · 1r ≡ u · 0r · s
       path = (λ i → ·Rid (q  i) i) ∙∙ sym (0LeftAnnihilates _)
                                    ∙∙ cong (_· s) (sym (0RightAnnihilates _))

   Surχ : isSurjection (f χ)
   Surχ a = PT.rec propTruncIsProp (λ x → PT.∣ [ x .fst ] , x .snd ∣) (surχ a)

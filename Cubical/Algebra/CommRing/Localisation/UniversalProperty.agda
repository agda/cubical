-- We define what it means to satisfy the universal property
-- of localisation and show that the localisation in Base satisfies
-- it. We will also show that the localisation is uniquely determined
-- by the universal property, and give sufficient criteria for
-- satisfying the universal property.

{-# OPTIONS --safe #-}
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
open import Cubical.Tactics.CommRingSolver
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Localisation.Base

open import Cubical.HITs.SetQuotients as SQ
open import Cubical.HITs.PropositionalTruncation as PT

open Iso

private
  variable
    ℓ ℓ' : Level


module _ (R' : CommRing ℓ) (S' : ℙ (fst R')) (SMultClosedSubset : isMultClosedSubset R' S') where
 open isMultClosedSubset
 private R = fst R'
 open CommRingStr (snd R') hiding (is-set)
 open RingTheory (CommRing→Ring R')
 open IsRingHom



 hasLocUniversalProp : (A : CommRing ℓ) (φ : CommRingHom R' A)
                     → (∀ s → s ∈ S' → fst φ s ∈ A ˣ)
                     → Type (ℓ-suc ℓ)
 hasLocUniversalProp A φ _ = (B : CommRing ℓ) (ψ : CommRingHom R' B)
                           → (∀ s → s ∈ S' → fst ψ s ∈ B ˣ)
                           → ∃![ χ ∈ CommRingHom A B ] (fst χ) ∘ (fst φ) ≡ (fst ψ)

 isPropUniversalProp : (A : CommRing ℓ) (φ : CommRingHom R' A)
                     → (φS⊆Aˣ : ∀ s → s ∈ S' → fst φ s ∈ A ˣ)
                     → isProp (hasLocUniversalProp A φ φS⊆Aˣ)
 isPropUniversalProp A φ φS⊆Aˣ = isPropΠ3 (λ _ _ _ → isPropIsContr)

 -- S⁻¹R has the universal property
 module S⁻¹RUniversalProp where
  open Loc R' S' SMultClosedSubset
  _/1 : R → S⁻¹R
  r /1 = [ r , 1r , SMultClosedSubset .containsOne ]

  /1AsCommRingHom : CommRingHom R' S⁻¹RAsCommRing
  fst /1AsCommRingHom = _/1
  snd /1AsCommRingHom =
    makeIsRingHom
      refl
      (λ r r' → cong [_] (≡-× (cong₂ (_+_) (sym (·IdR r)) (sym (·IdR r')))
                              (Σ≡Prop (λ x → S' x .snd) (sym (·IdL 1r)))))
      (λ _ _ → cong [_] (≡-× refl (Σ≡Prop (λ x → S' x .snd) (sym (·IdL 1r)))))

  S⁻¹Rˣ = S⁻¹RAsCommRing ˣ
  S/1⊆S⁻¹Rˣ : ∀ s → s ∈ S' → (s /1) ∈ S⁻¹Rˣ
  S/1⊆S⁻¹Rˣ s s∈S' = [ 1r , s , s∈S' ] , eq/ _ _ ((1r , SMultClosedSubset .containsOne) , solve! R')

  S⁻¹RHasUniversalProp : hasLocUniversalProp S⁻¹RAsCommRing /1AsCommRingHom S/1⊆S⁻¹Rˣ
  S⁻¹RHasUniversalProp B' ψ ψS⊆Bˣ = (χ , funExt χcomp) , χunique
   where
   B = fst B'
   open CommRingStr (snd B') renaming  ( is-set to Bset ; _·_ to _·B_ ; 1r to 1b
                                       ; _+_ to _+B_
                                       ; ·Assoc to ·B-assoc ; ·Comm to ·B-comm
                                       ; ·IdL to ·B-lid ; ·IdR to ·B-rid
                                       ; ·DistL+ to ·B-ldist-+)
   open Units B' renaming (Rˣ to Bˣ ; RˣMultClosed to BˣMultClosed ; RˣContainsOne to BˣContainsOne)
   open RingTheory (CommRing→Ring B') renaming (·-assoc2 to ·B-assoc2)
   open CommRingTheory B' renaming (·CommAssocl to ·B-commAssocl ; ·CommAssocSwap to ·B-commAssocSwap)

   ψ₀ = fst ψ
   module ψ = IsRingHom (snd ψ)

   χ : CommRingHom S⁻¹RAsCommRing B'
   fst χ = SQ.rec Bset fχ fχcoh
    where
    fχ : R × S → B
    fχ (r , s , s∈S') = (fst ψ r) ·B ((fst ψ s) ⁻¹) ⦃ ψS⊆Bˣ s s∈S' ⦄
    fχcoh : (a b : R × S) → a ≈ b → fχ a ≡ fχ b
    fχcoh (r , s , s∈S') (r' , s' , s'∈S') ((u , u∈S') , p) = instancepath
     ⦃ ψS⊆Bˣ s s∈S' ⦄ ⦃ ψS⊆Bˣ s' s'∈S' ⦄ ⦃ ψS⊆Bˣ (u · s · s')
            (SMultClosedSubset .multClosed (SMultClosedSubset .multClosed u∈S' s∈S') s'∈S') ⦄
     ⦃ BˣMultClosed _ _ ⦃ ψS⊆Bˣ (u · s) (SMultClosedSubset .multClosed u∈S' s∈S') ⦄
                        ⦃ ψS⊆Bˣ s' s'∈S' ⦄ ⦄
     ⦃ ψS⊆Bˣ (u · s) (SMultClosedSubset .multClosed u∈S' s∈S') ⦄
     where
     -- only a few individual steps can be solved by the ring solver yet
     instancepath : ⦃ _ : ψ₀ s ∈ Bˣ ⦄ ⦃ _ : ψ₀ s' ∈ Bˣ ⦄
                    ⦃ _ : ψ₀ (u · s · s') ∈ Bˣ ⦄ ⦃ _ : ψ₀ (u · s) ·B ψ₀ s' ∈ Bˣ ⦄
                    ⦃ _ : ψ₀ (u · s) ∈ Bˣ ⦄
                  → ψ₀ r ·B ψ₀ s ⁻¹ ≡ ψ₀ r' ·B ψ₀ s' ⁻¹
     instancepath = ψ₀ r ·B ψ₀ s ⁻¹

                  ≡⟨ sym (·B-rid _) ⟩

                    ψ₀ r ·B ψ₀ s ⁻¹ ·B 1b

                  ≡⟨ cong (ψ₀ r ·B ψ₀ s ⁻¹ ·B_) (sym (·-rinv _)) ⟩

                    ψ₀ r ·B ψ₀ s ⁻¹ ·B (ψ₀ (u · s · s') ·B ψ₀ (u · s · s') ⁻¹)

                  ≡⟨ ·B-assoc _ _ _ ⟩

                    ψ₀ r ·B ψ₀ s ⁻¹ ·B ψ₀ (u · s · s') ·B ψ₀ (u · s · s') ⁻¹

                  ≡⟨ cong (λ x → ψ₀ r ·B ψ₀ s ⁻¹ ·B x ·B ψ₀ (u · s · s') ⁻¹) (ψ.pres· _ _) ⟩

                    ψ₀ r ·B ψ₀ s ⁻¹ ·B (ψ₀ (u · s) ·B ψ₀ s') ·B ψ₀ (u · s · s') ⁻¹

                  ≡⟨ cong (_·B ψ₀ (u · s · s') ⁻¹) (·B-assoc _ _ _) ⟩

                    ψ₀ r ·B ψ₀ s ⁻¹ ·B ψ₀ (u · s) ·B ψ₀ s' ·B ψ₀ (u · s · s') ⁻¹

                  ≡⟨ cong (λ x → ψ₀ r ·B ψ₀ s ⁻¹ ·B x ·B ψ₀ s' ·B ψ₀ (u · s · s') ⁻¹)
                          (ψ.pres· _ _) ⟩

                    ψ₀ r ·B ψ₀ s ⁻¹ ·B (ψ₀ u ·B ψ₀ s) ·B ψ₀ s' ·B ψ₀ (u · s · s') ⁻¹

                  ≡⟨ cong (λ x → x ·B ψ₀ s' ·B ψ₀ (u · s · s') ⁻¹) (·B-commAssocSwap _ _ _ _) ⟩

                    ψ₀ r ·B ψ₀ u ·B (ψ₀ s ⁻¹ ·B ψ₀ s) ·B ψ₀ s' ·B ψ₀ (u · s · s') ⁻¹

                  ≡⟨ (λ i → ·B-comm (ψ₀ r) (ψ₀ u) i ·B (·-linv (ψ₀ s) i)
                                                      ·B ψ₀ s' ·B ψ₀ (u · s · s') ⁻¹) ⟩

                    ψ₀ u ·B ψ₀ r ·B 1b ·B ψ₀ s' ·B ψ₀ (u · s · s') ⁻¹

                  ≡⟨ (λ i → (·B-rid (sym (ψ.pres· u r) i) i) ·B ψ₀ s' ·B ψ₀ (u · s · s') ⁻¹) ⟩

                    ψ₀ (u · r) ·B ψ₀ s' ·B ψ₀ (u · s · s') ⁻¹

                  ≡⟨ cong (_·B ψ₀ (u · s · s') ⁻¹) (sym (ψ.pres· _ _)) ⟩

                    ψ₀ (u · r · s') ·B ψ₀ (u · s · s') ⁻¹

                  ≡⟨ cong (λ x → ψ₀ x ·B ψ₀ (u · s · s') ⁻¹) p ⟩

                    ψ₀ (u · r' · s) ·B ψ₀ (u · s · s') ⁻¹

                  ≡⟨ cong (_·B ψ₀ (u · s · s') ⁻¹) (ψ.pres· _ _) ⟩

                    ψ₀ (u · r') ·B ψ₀ s ·B ψ₀ (u · s · s') ⁻¹

                  ≡⟨ cong (λ x → x ·B ψ₀ s ·B ψ₀ (u · s · s') ⁻¹) (ψ.pres· _ _) ⟩

                    ψ₀ u ·B ψ₀ r' ·B ψ₀ s ·B ψ₀ (u · s · s') ⁻¹

                  ≡⟨ cong (_·B ψ₀ (u · s · s') ⁻¹) (sym (·B-assoc _ _ _)) ⟩

                    ψ₀ u ·B (ψ₀ r' ·B ψ₀ s) ·B ψ₀ (u · s · s') ⁻¹

                  ≡⟨ cong (_·B ψ₀ (u · s · s') ⁻¹) (·B-commAssocl _ _ _) ⟩

                    ψ₀ r' ·B (ψ₀ u ·B ψ₀ s) ·B ψ₀ (u · s · s') ⁻¹

                  ≡⟨ cong (λ x → ψ₀ r' ·B x ·B ψ₀ (u · s · s') ⁻¹) (sym (ψ.pres· _ _)) ⟩

                    ψ₀ r' ·B ψ₀ (u · s) ·B ψ₀ (u · s · s') ⁻¹

                  ≡⟨ cong (ψ₀ r' ·B ψ₀ (u · s) ·B_) (unitCong (ψ.pres· _ _)) ⟩

                    ψ₀ r' ·B ψ₀ (u · s) ·B (ψ₀ (u · s) ·B ψ₀ s') ⁻¹

                  ≡⟨ cong (ψ₀ r' ·B ψ₀ (u · s) ·B_) (⁻¹-dist-· _ _) ⟩

                    ψ₀ r' ·B ψ₀ (u · s) ·B (ψ₀ (u · s) ⁻¹ ·B ψ₀ s' ⁻¹)

                  ≡⟨ ·B-assoc2 _ _ _ _ ⟩

                    ψ₀ r' ·B (ψ₀ (u · s) ·B ψ₀ (u · s) ⁻¹) ·B ψ₀ s' ⁻¹

                  ≡⟨ cong (λ x → ψ₀ r' ·B x ·B ψ₀ s' ⁻¹) (·-rinv _) ⟩

                    ψ₀ r' ·B 1b ·B ψ₀ s' ⁻¹

                  ≡⟨ cong (_·B ψ₀ s' ⁻¹) (·B-rid _) ⟩

                    ψ₀ r' ·B ψ₀ s' ⁻¹ ∎

   snd χ =
    makeIsRingHom
      (instancepres1χ ⦃ ψS⊆Bˣ 1r (SMultClosedSubset .containsOne) ⦄ ⦃ BˣContainsOne ⦄)
      (elimProp2 (λ _ _ _ _ → Bset _ _ _ _) pres+[])
      (elimProp2 (λ _ _ _ _ → Bset _ _ _ _) pres·[])
    where
    instancepres1χ : ⦃ _ : ψ₀ 1r ∈ Bˣ ⦄ ⦃ _ : 1b ∈ Bˣ ⦄
                     → ψ₀ 1r ·B (ψ₀ 1r) ⁻¹ ≡ 1b
    instancepres1χ = (λ i → (ψ.pres1 i) ·B (unitCong (ψ.pres1) i))
                   ∙ (λ i → ·B-lid (1⁻¹≡1 i) i)

    pres+[] : (a b : R × S) → fst χ ([ a ] +ₗ [ b ]) ≡ (fst χ [ a ]) +B (fst χ [ b ])
    pres+[] (r , s , s∈S') (r' , s' , s'∈S') = instancepath
     ⦃ ψS⊆Bˣ s s∈S' ⦄ ⦃ ψS⊆Bˣ s' s'∈S' ⦄ ⦃ ψS⊆Bˣ (s · s') (SMultClosedSubset .multClosed s∈S' s'∈S') ⦄
     ⦃ BˣMultClosed _ _ ⦃ ψS⊆Bˣ s s∈S' ⦄ ⦃ ψS⊆Bˣ s' s'∈S' ⦄ ⦄
     where
     -- only a few individual steps can be solved by the ring solver yet
     instancepath : ⦃ _ : ψ₀ s ∈ Bˣ ⦄ ⦃ _ : ψ₀ s' ∈ Bˣ ⦄
                    ⦃ _ : ψ₀ (s · s') ∈ Bˣ ⦄ ⦃ _ : ψ₀ s ·B ψ₀ s' ∈ Bˣ ⦄
                → ψ₀ (r · s' + r' · s) ·B ψ₀ (s · s') ⁻¹ ≡ ψ₀ r ·B ψ₀ s ⁻¹ +B ψ₀ r' ·B ψ₀ s' ⁻¹
     instancepath =
            ψ₀ (r · s' + r' · s) ·B ψ₀ (s · s') ⁻¹

          ≡⟨ (λ i → ψ.pres+ (r · s') (r' · s) i ·B unitCong (ψ.pres· s s') i) ⟩

            (ψ₀ (r · s') +B ψ₀ (r' · s)) ·B (ψ₀ s ·B ψ₀ s') ⁻¹

          ≡⟨ (λ i → (ψ.pres· r s' i +B ψ.pres· r' s i) ·B ⁻¹-dist-· (ψ₀ s) (ψ₀ s') i) ⟩

            (ψ₀ r ·B ψ₀ s' +B ψ₀ r' ·B ψ₀ s) ·B (ψ₀ s ⁻¹ ·B ψ₀ s' ⁻¹)

          ≡⟨ ·B-ldist-+ _ _ _ ⟩

            ψ₀ r ·B ψ₀ s' ·B (ψ₀ s ⁻¹ ·B ψ₀ s' ⁻¹) +B ψ₀ r' ·B ψ₀ s ·B (ψ₀ s ⁻¹ ·B ψ₀ s' ⁻¹)

          ≡⟨ (λ i → ·B-commAssocSwap (ψ₀ r) (ψ₀ s') (ψ₀ s ⁻¹) (ψ₀ s' ⁻¹) i
                 +B ·B-assoc2 (ψ₀ r') (ψ₀ s) (ψ₀ s ⁻¹) (ψ₀ s' ⁻¹) i) ⟩

            ψ₀ r ·B ψ₀ s ⁻¹ ·B (ψ₀ s' ·B ψ₀ s' ⁻¹) +B ψ₀ r' ·B (ψ₀ s ·B ψ₀ s ⁻¹) ·B ψ₀ s' ⁻¹

          ≡⟨ (λ i → ψ₀ r ·B ψ₀ s ⁻¹ ·B (·-rinv (ψ₀ s') i)
                 +B ψ₀ r' ·B (·-rinv (ψ₀ s) i) ·B ψ₀ s' ⁻¹) ⟩

            ψ₀ r ·B ψ₀ s ⁻¹ ·B 1b +B ψ₀ r' ·B 1b ·B ψ₀ s' ⁻¹

          ≡⟨ (λ i → ·B-rid (ψ₀ r ·B ψ₀ s ⁻¹) i +B ·B-rid (ψ₀ r') i ·B ψ₀ s' ⁻¹) ⟩

            ψ₀ r ·B ψ₀ s ⁻¹ +B ψ₀ r' ·B ψ₀ s' ⁻¹ ∎

    pres·[] : (a b : R × S) → fst χ ([ a ] ·ₗ [ b ]) ≡ (fst χ [ a ]) ·B (fst χ [ b ])
    pres·[] (r , s , s∈S') (r' , s' , s'∈S') = instancepath
     ⦃ ψS⊆Bˣ s s∈S' ⦄ ⦃ ψS⊆Bˣ s' s'∈S' ⦄ ⦃ ψS⊆Bˣ (s · s') (SMultClosedSubset .multClosed s∈S' s'∈S') ⦄
     ⦃ BˣMultClosed _ _ ⦃ ψS⊆Bˣ s s∈S' ⦄ ⦃ ψS⊆Bˣ s' s'∈S' ⦄ ⦄
     where
     -- only a few individual steps can be solved by the ring solver yet
     instancepath : ⦃ _ : ψ₀ s ∈ Bˣ ⦄ ⦃ _ : ψ₀ s' ∈ Bˣ ⦄
                    ⦃ _ : ψ₀ (s · s') ∈ Bˣ ⦄ ⦃ _ : ψ₀ s ·B ψ₀ s' ∈ Bˣ ⦄
                  → ψ₀ (r · r') ·B ψ₀ (s · s') ⁻¹ ≡ (ψ₀ r ·B ψ₀ s ⁻¹) ·B (ψ₀ r' ·B ψ₀ s' ⁻¹)
     instancepath = ψ₀ (r · r') ·B ψ₀ (s · s') ⁻¹

                  ≡⟨ (λ i → ψ.pres· r r' i ·B unitCong (ψ.pres· s s') i) ⟩

                    ψ₀ r ·B ψ₀ r' ·B (ψ₀ s ·B ψ₀ s') ⁻¹

                  ≡⟨ cong (ψ₀ r ·B ψ₀ r' ·B_) (⁻¹-dist-· _ _) ⟩

                    ψ₀ r ·B ψ₀ r' ·B (ψ₀ s ⁻¹ ·B ψ₀ s' ⁻¹)

                  ≡⟨ ·B-commAssocSwap _ _ _ _ ⟩

                    ψ₀ r ·B ψ₀ s ⁻¹ ·B (ψ₀ r' ·B ψ₀ s' ⁻¹) ∎


   χcomp : (r : R) → fst χ (r /1) ≡ ψ₀ r
   χcomp = instanceχcomp ⦃ ψS⊆Bˣ 1r (SMultClosedSubset .containsOne) ⦄ ⦃ Units.RˣContainsOne B' ⦄
    where
    instanceχcomp : ⦃ _ : ψ₀ 1r ∈ Bˣ ⦄ ⦃ _ : 1b ∈ Bˣ ⦄
                    (r : R) → ψ₀ r ·B (ψ₀ 1r) ⁻¹ ≡ ψ₀ r
    instanceχcomp r = ψ₀ r ·B (ψ₀ 1r) ⁻¹ ≡⟨ cong (ψ₀ r ·B_) (unitCong (ψ.pres1)) ⟩
                      ψ₀ r ·B 1b ⁻¹      ≡⟨ cong (ψ₀ r ·B_) 1⁻¹≡1 ⟩
                      ψ₀ r ·B 1b         ≡⟨ ·B-rid _ ⟩
                      ψ₀ r ∎


   χunique : (y : Σ[ χ' ∈ CommRingHom S⁻¹RAsCommRing B' ] fst χ' ∘ _/1 ≡ ψ₀)
           → (χ , funExt χcomp) ≡ y
   χunique (χ' , χ'/1≡ψ) = Σ≡Prop (λ x → isSetΠ (λ _ → Bset) _ _) (RingHom≡ fχ≡fχ')
    where
    open CommRingHomTheory {A' = S⁻¹RAsCommRing} {B' = B'} χ'
                          renaming (φ[x⁻¹]≡φ[x]⁻¹ to χ'[x⁻¹]≡χ'[x]⁻¹)

    module χ' = IsRingHom (χ' .snd)

    []-path : (a : R × S) → fst χ [ a ] ≡ fst χ' [ a ]
    []-path (r , s , s∈S') = instancepath ⦃ ψS⊆Bˣ s s∈S' ⦄ ⦃ S/1⊆S⁻¹Rˣ s s∈S' ⦄
                                          ⦃ RingHomRespInv _ ⦃ S/1⊆S⁻¹Rˣ s s∈S' ⦄ ⦄
     where
     open Units S⁻¹RAsCommRing renaming (_⁻¹ to _⁻¹ˡ ; inverseUniqueness to S⁻¹RInverseUniqueness)
                               hiding (unitCong)

     s-inv : ⦃ s/1∈S⁻¹Rˣ : s /1 ∈ S⁻¹Rˣ ⦄ → s /1 ⁻¹ˡ ≡ [ 1r , s , s∈S' ]
     s-inv ⦃ s/1∈S⁻¹Rˣ ⦄ = PathPΣ (S⁻¹RInverseUniqueness (s /1) s/1∈S⁻¹Rˣ
                           (_ , eq/ _ _ ((1r , SMultClosedSubset .containsOne) , solve! R'))) .fst

     ·ₗ-path : [ r , s , s∈S' ] ≡   [ r , 1r , SMultClosedSubset .containsOne ]
                                 ·ₗ [ 1r , s , s∈S' ]
     ·ₗ-path = cong [_] (≡-× (sym (·IdR r)) (Σ≡Prop (λ x → S' x .snd) (sym (·IdL s))))

     instancepath : ⦃ _ : ψ₀ s ∈ Bˣ ⦄ ⦃ _ : s /1 ∈ S⁻¹Rˣ ⦄ ⦃ _ : fst χ' (s /1) ∈ Bˣ ⦄
                  → ψ₀ r ·B ψ₀ s ⁻¹ ≡ fst χ' [ r , s , s∈S' ]
     instancepath = ψ₀ r ·B ψ₀ s ⁻¹

                  ≡⟨ cong (ψ₀ r ·B_) (unitCong (cong (λ φ → φ s) (sym χ'/1≡ψ))) ⟩

                    ψ₀ r ·B fst χ' (s /1) ⁻¹

                  ≡⟨ cong (ψ₀ r ·B_) (sym (χ'[x⁻¹]≡χ'[x]⁻¹ _)) ⟩

                    ψ₀ r ·B fst χ' (s /1 ⁻¹ˡ)

                  ≡⟨ cong (λ x → ψ₀ r ·B fst χ' x) s-inv ⟩

                    ψ₀ r ·B fst χ' [ 1r , s , s∈S' ]

                  ≡⟨ cong (_·B fst χ' [ 1r , s , s∈S' ]) (cong (λ φ → φ r) (sym χ'/1≡ψ)) ⟩

                    fst χ' [ r , 1r , SMultClosedSubset .containsOne ] ·B fst χ' [ 1r , s , s∈S' ]

                  ≡⟨ sym (χ'.pres· _ _) ⟩

                    fst χ' ([ r , 1r , SMultClosedSubset .containsOne ] ·ₗ [ 1r , s , s∈S' ])

                  ≡⟨ cong (fst χ') (sym ·ₗ-path) ⟩

                    fst χ' [ r , s , s∈S' ] ∎

    fχ≡fχ' : fst χ ≡ fst χ'
    fχ≡fχ' = funExt (SQ.elimProp (λ _ → Bset _ _) []-path)


 -- sufficient conditions for having the universal property
 -- used as API in the leanprover-community/mathlib
 -- Corollary 3.2 in Atiyah-McDonald
 open S⁻¹RUniversalProp
 open Loc R' S' SMultClosedSubset

 record PathToS⁻¹R (A' : CommRing ℓ) (φ : CommRingHom R' A') : Type ℓ where
  constructor
   pathtoS⁻¹R
  open Units A' renaming (Rˣ to Aˣ)
  open CommRingStr (snd A') renaming (is-set to Aset ; 0r to 0a ; _·_ to _·A_)
  field
   φS⊆Aˣ : ∀ s → s ∈ S' → fst φ s ∈ Aˣ
   kerφ⊆annS : ∀ r → fst φ r ≡ 0a → ∃[ s ∈ S ] (s .fst) · r ≡ 0r
   surχ : ∀ a → ∃[ x ∈ R × S ] fst φ (x .fst) ·A (fst φ (x .snd .fst) ⁻¹) ⦃ φS⊆Aˣ _ (x .snd .snd) ⦄ ≡ a

 S⁻¹RCharEquiv : (A' : CommRing ℓ) (φ : CommRingHom R' A')
               → PathToS⁻¹R A' φ
               → CommRingEquiv S⁻¹RAsCommRing A'
 S⁻¹RCharEquiv A' φ cond = S⁻¹R≃A , χ .snd
  where
  open CommRingStr (snd A') renaming ( is-set to Aset ; 0r to 0a ; _·_ to _·A_ ; 1r to 1a
                                      ; ·IdR to ·A-rid)
  open Units A' renaming (Rˣ to Aˣ ; RˣInvClosed to AˣInvClosed)
  open PathToS⁻¹R ⦃...⦄
  private
   A = fst A'
   instance
    _ = cond
   χ = (S⁻¹RHasUniversalProp A' φ φS⊆Aˣ .fst .fst)
   open RingHomTheory χ

  S⁻¹R≃A : S⁻¹R ≃ A
  S⁻¹R≃A = fst χ , isEmbedding×isSurjection→isEquiv (Embχ , Surχ)
   where
   Embχ : isEmbedding (fst χ)
   Embχ = injEmbedding Aset (ker≡0→inj λ {x} → kerχ≡0 x)
    where
    kerχ≡0 : (r/s : S⁻¹R) → fst χ r/s ≡ 0a → r/s ≡ 0ₗ
    kerχ≡0 = SQ.elimProp (λ _ → isPropΠ λ _ → squash/ _ _) kerχ≡[]
     where
     kerχ≡[] : (a : R × S) → fst χ [ a ] ≡ 0a → [ a ] ≡ 0ₗ
     kerχ≡[] (r , s , s∈S') p = PT.rec (squash/ _ _) Σhelper
                                       (kerφ⊆annS r (UnitsAreNotZeroDivisors _ _ p))
      where
      instance
       _ : fst φ s ∈ Aˣ
       _ = φS⊆Aˣ s s∈S'
       _ : fst φ s ⁻¹ ∈ Aˣ
       _ = AˣInvClosed (fst φ s)

      Σhelper : Σ[ s ∈ S ] (s .fst) · r ≡ 0r → [ r , s , s∈S' ] ≡ 0ₗ
      Σhelper ((u , u∈S') , q) = eq/ _ _ ((u , u∈S') , path)
       where
       path : u · r · 1r ≡ u · 0r · s
       path = (λ i → ·IdR (q  i) i) ∙∙ sym (0LeftAnnihilates _)
                                    ∙∙ cong (_· s) (sym (0RightAnnihilates _))

   Surχ : isSurjection (fst χ)
   Surχ a = PT.rec isPropPropTrunc (λ x → PT.∣ [ x .fst ] , x .snd ∣₁) (surχ a)


 S⁻¹RChar : (A' : CommRing ℓ) (φ : CommRingHom R' A')
          → PathToS⁻¹R A' φ
          → S⁻¹RAsCommRing ≡ A'
 S⁻¹RChar A' φ cond = uaCommRing (S⁻¹RCharEquiv A' φ cond)

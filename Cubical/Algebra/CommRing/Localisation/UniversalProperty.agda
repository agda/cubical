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
 open Units hiding (_⁻¹)
 open RingHom
 --open Loc R' S' SMultClosedSubset


 hasLocUniversalProp : (A : CommRing {ℓ}) (φ : CommRingHom R' A)
                     → (∀ s → s ∈ S' → f φ s ∈ (Rˣ A))
                     → Type (ℓ-suc ℓ)
 hasLocUniversalProp A φ _ = (B : CommRing {ℓ}) (ψ : CommRingHom R' B)
                           → (∀ s → s ∈ S' → f ψ s ∈ (Rˣ B))
                           → ∃![ χ ∈ CommRingHom A B ] (f χ) ∘ (f φ) ≡ (f ψ)


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

 S⁻¹Rˣ = Rˣ S⁻¹RAsCommRing
 S/1⊆S⁻¹Rˣ : ∀ s → s ∈ S' → (s /1) ∈ S⁻¹Rˣ
 S/1⊆S⁻¹Rˣ s s∈S' = [ 1r , s , s∈S' ] , eq/ _ _ ((1r , SMultClosedSubset .containsOne) , path)
  where
  path : 1r · (s · 1r) · 1r ≡ 1r · 1r · (1r  · s)
  path = 1r · (s · 1r) · 1r ≡⟨ (λ i → ·-rid (·-lid (·-rid s i) i) i) ⟩
         s                  ≡⟨ (λ i → ·-lid (·-lid s (~ i)) (~ i)) ⟩
         1r · (1r  · s)     ≡⟨ cong (_· (1r · s)) (sym (·-lid _)) ⟩
         1r · 1r · (1r  · s) ∎

 -- S⁻¹RHasUniversalProp : hasLocUniversalProp S⁻¹RAsCommRing /1AsCommRingHom S/1⊆S⁻¹Rˣ
 -- S⁻¹RHasUniversalProp B' ψ ψS⊆Bˣ = ({!!} , {!!}) , {!!}
 --  where
 --  B = B' .fst
 --  open CommRingStr (B' .snd) renaming (is-set to Bset ; _·_ to _·B_)
 --  open Units B'

 --  χ : CommRingHom S⁻¹RAsCommRing B'
 --  f χ = SQ.rec Bset (λ { (r , s , s∈S') → (f ψ r) ·B ((f ψ s) ⁻¹) ⦃ ψS⊆Bˣ s s∈S' ⦄ }) {!!}
 --  pres1 χ = {!!}
 --  isHom+ χ = elimProp {!λ _ → Bset _ _!} {!!}
 --  isHom· χ = {!!}

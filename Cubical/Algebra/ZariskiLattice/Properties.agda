{-# OPTIONS --safe #-}
module Cubical.Algebra.ZariskiLattice.Properties where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Powerset using (ℙ ; ⊆-refl-consequence)
                                         renaming (_∈_ to _∈ₚ_ ; ∈-isProp to ∈ₚ-isProp)

import Cubical.Data.Empty as ⊥
open import Cubical.Data.Bool hiding (_≤_)
open import Cubical.Data.Nat renaming ( _+_ to _+ℕ_ ; _·_ to _·ℕ_ ; _^_ to _^ℕ_
                                      ; +-comm to +ℕ-comm ; +-assoc to +ℕ-assoc
                                      ; ·-assoc to ·ℕ-assoc ; ·-comm to ·ℕ-comm
                                      ; ·-identityʳ to ·ℕ-rid)
open import Cubical.Data.Sigma.Base
open import Cubical.Data.Sigma.Properties
open import Cubical.Data.FinData
open import Cubical.Data.Unit
open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary
open import Cubical.Relation.Binary.Order.Poset

open import Cubical.Algebra.Ring
open import Cubical.Algebra.Ring.Properties
open import Cubical.Algebra.Ring.BigOps
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.BinomialThm
open import Cubical.Algebra.CommRing.Ideal
open import Cubical.Algebra.CommRing.FGIdeal
open import Cubical.Algebra.CommRing.RadicalIdeal
open import Cubical.Tactics.CommRingSolver.Reflection
open import Cubical.Algebra.Semilattice
open import Cubical.Algebra.Lattice
open import Cubical.Algebra.DistLattice
open import Cubical.Algebra.DistLattice.Basis
open import Cubical.Algebra.DistLattice.BigOps
open import Cubical.Algebra.Matrix

open import Cubical.Algebra.ZariskiLattice.Base
open import Cubical.Algebra.ZariskiLattice.UniversalProperty

open import Cubical.HITs.SetQuotients as SQ
open import Cubical.HITs.PropositionalTruncation as PT


private variable ℓ : Level

module _ (R : CommRing ℓ) where
  open Iso
  open CommRingStr ⦃...⦄
  open DistLatticeStr ⦃...⦄
  open PosetStr ⦃...⦄

  open RingTheory (CommRing→Ring R)
  open Sum (CommRing→Ring R)
  open CommRingTheory R
  open Exponentiation R
  open BinomialThm R
  open CommIdeal R
  open RadicalIdeal R
  open isCommIdeal
  open ProdFin R

  open ZarLat R
  open ZarLatUniversalProp R
  open IsZarMap isZarMapD

  open JoinSemilattice (Lattice→JoinSemilattice (DistLattice→Lattice ZariskiLattice))
       using (IndPoset)

  private
    instance
      _ = R .snd
      _ = ZariskiLattice .snd
      _ = IndPoset .snd

    ⟨_⟩ : {n : ℕ} → FinVec (fst R) n → CommIdeal
    ⟨ V ⟩ = ⟨ V ⟩[ R ]

  unitLemmaZarLat : ∀ f → D f ≡ D 1r → f ∈ₚ R ˣ
  unitLemmaZarLat f Df≡D1 = PT.rec (∈ₚ-isProp (R ˣ) f) radicalHelper 1∈√⟨f⟩
    where
    D1≤Df : D 1r ≤ D f
    D1≤Df = subst (_≤ D f) Df≡D1 (is-refl _)

    1∈√⟨f⟩ : 1r ∈ √ ⟨ replicateFinVec 1 f ⟩
    1∈√⟨f⟩ = isEquivRel→effectiveIso ∼PropValued ∼EquivRel _ _ .fun D1≤Df .fst zero

    radicalHelper : Σ[ n ∈  ℕ ] 1r ^ n ∈ ⟨ replicateFinVec 1 f ⟩ → f ∈ₚ R ˣ
    radicalHelper (n , 1ⁿ∈⟨f⟩) = PT.rec (∈ₚ-isProp (R ˣ) f) fgHelper 1ⁿ∈⟨f⟩
      where
      fgHelper : Σ[ α ∈ FinVec (fst R) 1 ] 1r ^ n ≡ linearCombination R α (replicateFinVec 1 f)
               → f ∈ₚ R ˣ
      fgHelper (α , 1ⁿ≡α₀f+0) = α zero , path
        where
        useSolver : ∀ f α₀ → f · α₀ ≡ α₀ · f + 0r
        useSolver = solve R

        path : f · α zero ≡ 1r
        path = f · α zero      ≡⟨ useSolver _ _ ⟩
               α zero · f + 0r ≡⟨ sym 1ⁿ≡α₀f+0 ⟩
               1r ^ n          ≡⟨ 1ⁿ≡1 n ⟩
               1r ∎

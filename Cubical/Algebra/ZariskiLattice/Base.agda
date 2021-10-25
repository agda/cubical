{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.Algebra.ZariskiLattice.Base where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Transport
-- open import Cubical.Foundations.Structure
-- open import Cubical.Functions.FunExtEquiv

import Cubical.Data.Empty as ⊥
open import Cubical.Data.Bool
open import Cubical.Data.Nat renaming ( _+_ to _+ℕ_ ; _·_ to _·ℕ_
                                      ; +-comm to +ℕ-comm ; +-assoc to +ℕ-assoc
                                      ; ·-assoc to ·ℕ-assoc ; ·-comm to ·ℕ-comm)
open import Cubical.Data.Sigma.Base
open import Cubical.Data.Sigma.Properties
open import Cubical.Data.FinData
open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary
open import Cubical.Relation.Binary.Poset

open import Cubical.Algebra.Ring
open import Cubical.Algebra.Ring.Properties
open import Cubical.Algebra.Ring.BigOps
open import Cubical.Algebra.Algebra
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.BinomialThm
open import Cubical.Algebra.CommRing.Ideal
open import Cubical.Algebra.CommRing.FGIdeal
open import Cubical.Algebra.CommRing.RadicalIdeal
open import Cubical.Algebra.CommRing.Localisation.Base
open import Cubical.Algebra.CommRing.Localisation.UniversalProperty
open import Cubical.Algebra.CommRing.Localisation.InvertingElements
open import Cubical.Algebra.CommAlgebra.Base
open import Cubical.Algebra.CommAlgebra.Properties
open import Cubical.Algebra.CommAlgebra.Localisation
open import Cubical.Algebra.RingSolver.ReflectionSolving
open import Cubical.Algebra.Semilattice
open import Cubical.Algebra.Lattice
open import Cubical.Algebra.DistLattice
open import Cubical.Algebra.Matrix

open import Cubical.HITs.SetQuotients as SQ
open import Cubical.HITs.PropositionalTruncation as PT

open Iso
open BinaryRelation
open isEquivRel

private
  variable
    ℓ ℓ' : Level


module _ (R' : CommRing ℓ) where
 open CommRingStr (snd R')
 open RingTheory (CommRing→Ring R')
 open Sum (CommRing→Ring R')
 open CommRingTheory R'
 open Exponentiation R'
 open BinomialThm R'
 open CommIdeal R'
 open RadicalIdeal R'
 open isCommIdeal
 open ProdFin R'

 private
  R = fst R'
  A = Σ[ n ∈ ℕ ] (FinVec R n)
  ⟨_⟩ : {n : ℕ} → FinVec R n → CommIdeal
  ⟨ V ⟩ = ⟨ V ⟩[ R' ]

 _∼_ : A → A → Type (ℓ-suc ℓ)
 (_ , 𝔞) ∼ (_ , 𝔟) = √i ⟨ 𝔞 ⟩ ≡ √i ⟨ 𝔟 ⟩ --replace this by ≡ᴾ := ⊆ × ⊇ to preserve universe level

 ∼EquivRel : isEquivRel (_∼_)
 reflexive ∼EquivRel _ = refl
 symmetric ∼EquivRel _ _ = sym
 transitive ∼EquivRel _ _ _ = _∙_

 ZL : Type (ℓ-suc ℓ)
 ZL = A / _∼_

 _∨z_ : ZL → ZL → ZL
 _∨z_ = setQuotSymmBinOp (reflexive ∼EquivRel) (transitive ∼EquivRel)
                          (λ (_ , 𝔞) (_ , 𝔟) → (_ , 𝔞 ++Fin 𝔟))
   (λ (_ , 𝔞) (_ , 𝔟) → cong √i (FGIdealAddLemma _ 𝔞 𝔟 ∙∙ +iComm _ _ ∙∙ sym (FGIdealAddLemma _ 𝔟 𝔞)))
    λ (_ , 𝔞) (_ , 𝔟) (_ , 𝔠) 𝔞∼𝔟 → --need to show 𝔞∨𝔠 ∼ 𝔟∨𝔠
      √i ⟨ 𝔞 ++Fin 𝔠 ⟩      ≡⟨ cong √i (FGIdealAddLemma _ 𝔞 𝔠) ⟩
      √i (⟨ 𝔞 ⟩ +i ⟨ 𝔠 ⟩)    ≡⟨ sym (√+LContr _ _) ⟩
      √i (√i ⟨ 𝔞 ⟩ +i ⟨ 𝔠 ⟩) ≡⟨ cong (λ I → √i (I +i ⟨ 𝔠 ⟩)) 𝔞∼𝔟 ⟩
      √i (√i ⟨ 𝔟 ⟩ +i ⟨ 𝔠 ⟩) ≡⟨ √+LContr _ _ ⟩
      √i (⟨ 𝔟 ⟩ +i ⟨ 𝔠 ⟩)    ≡⟨ cong √i (sym (FGIdealAddLemma _ 𝔟 𝔠)) ⟩
      √i ⟨ 𝔟 ++Fin 𝔠 ⟩ ∎

 _∧z_ : ZL → ZL → ZL
 _∧z_ = setQuotSymmBinOp (reflexive ∼EquivRel) (transitive ∼EquivRel)
                          (λ (_ , 𝔞) (_ , 𝔟) → (_ , 𝔞 ··Fin 𝔟))
   (λ (_ , 𝔞) (_ , 𝔟) → cong √i (FGIdealMultLemma _ 𝔞 𝔟 ∙∙ ·iComm _ _ ∙∙ sym (FGIdealMultLemma _ 𝔟 𝔞)))
    λ (_ , 𝔞) (_ , 𝔟) (_ , 𝔠) 𝔞∼𝔟 → --need to show 𝔞∧𝔠 ∼ 𝔟∧𝔠
      √i ⟨ 𝔞 ··Fin 𝔠 ⟩      ≡⟨ cong √i (FGIdealMultLemma _ 𝔞 𝔠) ⟩
      √i (⟨ 𝔞 ⟩ ·i ⟨ 𝔠 ⟩)    ≡⟨ sym (√·LContr _ _) ⟩
      √i (√i ⟨ 𝔞 ⟩ ·i ⟨ 𝔠 ⟩) ≡⟨ cong (λ I → √i (I ·i ⟨ 𝔠 ⟩)) 𝔞∼𝔟 ⟩
      √i (√i ⟨ 𝔟 ⟩ ·i ⟨ 𝔠 ⟩) ≡⟨ √·LContr _ _ ⟩
      √i (⟨ 𝔟 ⟩ ·i ⟨ 𝔠 ⟩)    ≡⟨ cong √i (sym (FGIdealMultLemma _ 𝔟 𝔠)) ⟩
      √i ⟨ 𝔟 ··Fin 𝔠 ⟩ ∎

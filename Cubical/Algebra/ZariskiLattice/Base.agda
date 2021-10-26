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
                                      ; ·-assoc to ·ℕ-assoc ; ·-comm to ·ℕ-comm
                                      ; ·-identityʳ to ·ℕ-rid)
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
 (_ , α) ∼ (_ , β) = √i ⟨ α ⟩ ≡ √i ⟨ β ⟩ --replace this by ≡ᴾ := ⊆ × ⊇ to preserve universe level

 ∼EquivRel : isEquivRel (_∼_)
 reflexive ∼EquivRel _ = refl
 symmetric ∼EquivRel _ _ = sym
 transitive ∼EquivRel _ _ _ = _∙_

 ZL : Type (ℓ-suc ℓ)
 ZL = A / _∼_

 0z : ZL
 0z = [ 0 , (λ ()) ]

 1z : ZL
 1z = [ 1 , (λ { zero → 1r }) ]

 _∨z_ : ZL → ZL → ZL
 _∨z_ = setQuotSymmBinOp (reflexive ∼EquivRel) (transitive ∼EquivRel)
                          (λ (_ , α) (_ , β) → (_ , α ++Fin β))
   (λ (_ , α) (_ , β) → cong √i (FGIdealAddLemma _ α β ∙∙ +iComm _ _ ∙∙ sym (FGIdealAddLemma _ β α)))
    λ (_ , α) (_ , β) (_ , γ) α∼β → --need to show α∨γ ∼ β∨γ
      √i ⟨ α ++Fin γ ⟩      ≡⟨ cong √i (FGIdealAddLemma _ α γ) ⟩
      √i (⟨ α ⟩ +i ⟨ γ ⟩)    ≡⟨ sym (√+LContr _ _) ⟩
      √i (√i ⟨ α ⟩ +i ⟨ γ ⟩) ≡⟨ cong (λ I → √i (I +i ⟨ γ ⟩)) α∼β ⟩
      √i (√i ⟨ β ⟩ +i ⟨ γ ⟩) ≡⟨ √+LContr _ _ ⟩
      √i (⟨ β ⟩ +i ⟨ γ ⟩)    ≡⟨ cong √i (sym (FGIdealAddLemma _ β γ)) ⟩
      √i ⟨ β ++Fin γ ⟩ ∎

 _∧z_ : ZL → ZL → ZL
 _∧z_ = setQuotSymmBinOp (reflexive ∼EquivRel) (transitive ∼EquivRel)
                          (λ (_ , α) (_ , β) → (_ , α ··Fin β))
   (λ (_ , α) (_ , β) → cong √i (FGIdealMultLemma _ α β ∙∙ ·iComm _ _ ∙∙ sym (FGIdealMultLemma _ β α)))
    λ (_ , α) (_ , β) (_ , γ) α∼β → --need to show α∧γ ∼ β∧γ
      √i ⟨ α ··Fin γ ⟩       ≡⟨ cong √i (FGIdealMultLemma _ α γ) ⟩
      √i (⟨ α ⟩ ·i ⟨ γ ⟩)    ≡⟨ sym (√·LContr _ _) ⟩
      √i (√i ⟨ α ⟩ ·i ⟨ γ ⟩) ≡⟨ cong (λ I → √i (I ·i ⟨ γ ⟩)) α∼β ⟩
      √i (√i ⟨ β ⟩ ·i ⟨ γ ⟩) ≡⟨ √·LContr _ _ ⟩
      √i (⟨ β ⟩ ·i ⟨ γ ⟩)    ≡⟨ cong √i (sym (FGIdealMultLemma _ β γ)) ⟩
      √i ⟨ β ··Fin γ ⟩ ∎

 -- join axioms
 ∨zAssoc : ∀ (𝔞 𝔟 𝔠 : ZL) → 𝔞 ∨z (𝔟 ∨z 𝔠) ≡ (𝔞 ∨z 𝔟) ∨z 𝔠
 ∨zAssoc = SQ.elimProp3 (λ _ _ _ → squash/ _ _)
          λ (_ , α) (_ , β) (_ , γ) → eq/ _ _ (cong √i (IdealAddAssoc _ _ _ _))

 ∨zComm : ∀ (𝔞 𝔟 : ZL) → 𝔞 ∨z 𝔟 ≡ 𝔟 ∨z 𝔞
 ∨zComm = SQ.elimProp2 (λ _ _ → squash/ _ _)
        λ (_ , α) (_ , β) → eq/ _ _ (cong √i (FGIdealAddLemma _ α β ∙∙ +iComm _ _ ∙∙ sym (FGIdealAddLemma _ β α)))

 ∨zLid : ∀ (𝔞 : ZL) → 0z ∨z 𝔞 ≡ 𝔞
 ∨zLid = SQ.elimProp (λ _ → squash/ _ _) λ _ → eq/ _ _ refl

 ∨zRid : ∀ (𝔞 : ZL) → 𝔞 ∨z 0z ≡ 𝔞
 ∨zRid _ = ∨zComm _ _ ∙ ∨zLid _


 -- -- meet axioms
 ∧zAssoc : ∀ (𝔞 𝔟 𝔠 : ZL) → 𝔞 ∧z (𝔟 ∧z 𝔠) ≡ (𝔞 ∧z 𝔟) ∧z 𝔠
 ∧zAssoc = SQ.elimProp3 (λ _ _ _ → squash/ _ _)
         λ (_ , α) (_ , β) (_ , γ) → eq/ _ _
           (√i ⟨ α ··Fin (β ··Fin γ) ⟩     ≡⟨ cong √i (FGIdealMultLemma _ _ _) ⟩
            √i (⟨ α ⟩ ·i ⟨ β ··Fin γ ⟩)    ≡⟨ cong (λ x → √i (⟨ α ⟩ ·i x)) (FGIdealMultLemma _ _ _) ⟩
            √i (⟨ α ⟩ ·i (⟨ β ⟩ ·i ⟨ γ ⟩)) ≡⟨ cong √i (·iAssoc _ _ _) ⟩
            √i ((⟨ α ⟩ ·i ⟨ β ⟩) ·i ⟨ γ ⟩) ≡⟨ cong (λ x → √i (x ·i ⟨ γ ⟩)) (sym (FGIdealMultLemma _ _ _)) ⟩
            √i (⟨ α ··Fin β ⟩ ·i ⟨ γ ⟩)    ≡⟨ cong √i (sym (FGIdealMultLemma _ _ _)) ⟩
            √i ⟨ (α ··Fin β) ··Fin γ ⟩     ∎)

 ∧zComm : ∀ (𝔞 𝔟 : ZL) → 𝔞 ∧z 𝔟 ≡ 𝔟 ∧z 𝔞
 ∧zComm = SQ.elimProp2 (λ _ _ → squash/ _ _)
        λ (_ , α) (_ , β) → eq/ _ _ (cong √i (FGIdealMultLemma _ α β ∙∙ ·iComm _ _ ∙∙ sym (FGIdealMultLemma _ β α)))


 -- ∧zLid : ∀ (𝔞 : ZL) → 1z ∧z 𝔞 ≡ 𝔞
 -- ∧zLid = SQ.elimProp (λ _ → squash/ _ _) λ (_ , α) → {!!} --eq/ _ _ {!!}


 ∧zRid : ∀ (𝔞 : ZL) → 𝔞 ∧z 1z ≡ 𝔞
 ∧zRid = SQ.elimProp (λ _ → squash/ _ _) λ (_ , α) → {!!} --cong [_] (ΣPathP (·ℕ-rid _ , {!!}))


 -- absorption and distributivity
 ∧zAbsorb∨z : ∀ (𝔞 𝔟 : ZL) → 𝔞 ∧z (𝔞 ∨z 𝔟) ≡ 𝔞
 ∧zAbsorb∨z = SQ.elimProp2 (λ _ _ → squash/ _ _)
            λ (_ , α) (_ , β) → eq/ _ _
              (√i ⟨ α ··Fin (α ++Fin β) ⟩     ≡⟨ cong √i (FGIdealMultLemma _ α (α ++Fin β)) ⟩
               √i (⟨ α ⟩ ·i ⟨ α ++Fin β ⟩)    ≡⟨ cong (λ x → √i (⟨ α ⟩ ·i x)) (FGIdealAddLemma _ α β) ⟩
               √i (⟨ α ⟩ ·i (⟨ α ⟩ +i ⟨ β ⟩)) ≡⟨ √·Absorb+ _ _ ⟩
               √i ⟨ α ⟩ ∎)

 ∧zLDist∨z : ∀ (𝔞 𝔟 𝔠 : ZL) → 𝔞 ∧z (𝔟 ∨z 𝔠) ≡ (𝔞 ∧z 𝔟) ∨z (𝔞 ∧z 𝔠)
 ∧zLDist∨z = SQ.elimProp3 (λ _ _ _ → squash/ _ _)
           λ (_ , α) (_ , β) (_ , γ) → eq/ _ _
             (√i ⟨ α ··Fin (β ++Fin γ) ⟩            ≡⟨ cong √i (FGIdealMultLemma _ _ _) ⟩
              √i (⟨ α ⟩ ·i ⟨ β ++Fin γ ⟩)           ≡⟨ cong (λ x → √i (⟨ α ⟩ ·i x)) (FGIdealAddLemma _ _ _) ⟩
              √i (⟨ α ⟩ ·i (⟨ β ⟩ +i ⟨ γ ⟩))        ≡⟨ cong √i (·iRdist+i _ _ _) ⟩ -- L/R-dist are swapped
                                                                                   -- in Lattices vs Rings
              √i (⟨ α ⟩ ·i ⟨ β ⟩ +i ⟨ α ⟩ ·i ⟨ γ ⟩) ≡⟨ cong₂ (λ x y → √i (x +i y))
                                                             (sym (FGIdealMultLemma _ _ _))
                                                             (sym (FGIdealMultLemma _ _ _)) ⟩
              √i (⟨ α ··Fin β ⟩ +i ⟨ α ··Fin γ ⟩)   ≡⟨ cong √i (sym (FGIdealAddLemma _ _ _)) ⟩
              √i ⟨ (α ··Fin β) ++Fin (α ··Fin γ) ⟩  ∎)

{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.Algebra.ZariskiLattice.Base where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Powerset using (ℙ ; ⊆-refl-consequence)
                                         renaming (_∈_ to _∈ₚ_ ; subst-∈ to subst-∈ₚ)

import Cubical.Data.Empty as ⊥
open import Cubical.Data.Bool
open import Cubical.Data.Nat renaming ( _+_ to _+ℕ_ ; _·_ to _·ℕ_
                                      ; +-comm to +ℕ-comm ; +-assoc to +ℕ-assoc
                                      ; ·-assoc to ·ℕ-assoc ; ·-comm to ·ℕ-comm
                                      ; ·-identityʳ to ·ℕ-rid)
open import Cubical.Data.Sigma.Base
open import Cubical.Data.Sigma.Properties
open import Cubical.Data.FinData
open import Cubical.Data.Unit
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
open import Cubical.Algebra.CommRing.Localisation.PullbackSquare
open import Cubical.Algebra.CommAlgebra.Base
open import Cubical.Algebra.CommAlgebra.Properties
open import Cubical.Algebra.CommAlgebra.Localisation
open import Cubical.Algebra.CommAlgebra.Unit
open import Cubical.Algebra.RingSolver.Reflection
open import Cubical.Algebra.Semilattice
open import Cubical.Algebra.Lattice
open import Cubical.Algebra.DistLattice
open import Cubical.Algebra.DistLattice.Basis
open import Cubical.Algebra.DistLattice.BigOps
open import Cubical.Algebra.Matrix

open import Cubical.Categories.Category.Base hiding (_[_,_])
open import Cubical.Categories.Functor
open import Cubical.Categories.Limits.Pullback
open import Cubical.Categories.Instances.CommAlgebras
open import Cubical.Categories.Instances.DistLattice
open import Cubical.Categories.Instances.Semilattice
open import Cubical.Categories.DistLatticeSheaf

open import Cubical.HITs.SetQuotients as SQ
open import Cubical.HITs.PropositionalTruncation as PT

open Iso
open BinaryRelation
open isEquivRel

private
  variable
    ℓ ℓ' : Level


module ZarLat (R' : CommRing ℓ) where
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
 (_ , α) ∼ (_ , β) = √ ⟨ α ⟩ ≡ √ ⟨ β ⟩

 ∼EquivRel : isEquivRel (_∼_)
 reflexive ∼EquivRel _ = refl
 symmetric ∼EquivRel _ _ = sym
 transitive ∼EquivRel _ _ _ = _∙_

 ZL : Type (ℓ-suc ℓ)
 ZL = A / _∼_

 0z : ZL
 0z = [ 0 , (λ ()) ]

 1z : ZL
 1z = [ 1 , (replicateFinVec 1 1r) ]

 _∨z_ : ZL → ZL → ZL
 _∨z_ = setQuotSymmBinOp (reflexive ∼EquivRel) (transitive ∼EquivRel)
                          (λ (_ , α) (_ , β) → (_ , α ++Fin β))
   (λ (_ , α) (_ , β) → cong √ (FGIdealAddLemma _ α β ∙∙ +iComm _ _ ∙∙ sym (FGIdealAddLemma _ β α)))
    λ (_ , α) (_ , β) (_ , γ) α∼β → --need to show α∨γ ∼ β∨γ
      √ ⟨ α ++Fin γ ⟩      ≡⟨ cong √ (FGIdealAddLemma _ α γ) ⟩
      √ (⟨ α ⟩ +i ⟨ γ ⟩)    ≡⟨ sym (√+LContr _ _) ⟩
      √ (√ ⟨ α ⟩ +i ⟨ γ ⟩) ≡⟨ cong (λ I → √ (I +i ⟨ γ ⟩)) α∼β ⟩
      √ (√ ⟨ β ⟩ +i ⟨ γ ⟩) ≡⟨ √+LContr _ _ ⟩
      √ (⟨ β ⟩ +i ⟨ γ ⟩)    ≡⟨ cong √ (sym (FGIdealAddLemma _ β γ)) ⟩
      √ ⟨ β ++Fin γ ⟩ ∎

 _∧z_ : ZL → ZL → ZL
 _∧z_ = setQuotSymmBinOp (reflexive ∼EquivRel) (transitive ∼EquivRel)
                          (λ (_ , α) (_ , β) → (_ , α ··Fin β))
   (λ (_ , α) (_ , β) → cong √ (FGIdealMultLemma _ α β ∙∙ ·iComm _ _ ∙∙ sym (FGIdealMultLemma _ β α)))
    λ (_ , α) (_ , β) (_ , γ) α∼β → --need to show α∧γ ∼ β∧γ
      √ ⟨ α ··Fin γ ⟩       ≡⟨ cong √ (FGIdealMultLemma _ α γ) ⟩
      √ (⟨ α ⟩ ·i ⟨ γ ⟩)    ≡⟨ sym (√·LContr _ _) ⟩
      √ (√ ⟨ α ⟩ ·i ⟨ γ ⟩) ≡⟨ cong (λ I → √ (I ·i ⟨ γ ⟩)) α∼β ⟩
      √ (√ ⟨ β ⟩ ·i ⟨ γ ⟩) ≡⟨ √·LContr _ _ ⟩
      √ (⟨ β ⟩ ·i ⟨ γ ⟩)    ≡⟨ cong √ (sym (FGIdealMultLemma _ β γ)) ⟩
      √ ⟨ β ··Fin γ ⟩ ∎

 -- join axioms
 ∨zAssoc : ∀ (𝔞 𝔟 𝔠 : ZL) → 𝔞 ∨z (𝔟 ∨z 𝔠) ≡ (𝔞 ∨z 𝔟) ∨z 𝔠
 ∨zAssoc = SQ.elimProp3 (λ _ _ _ → squash/ _ _)
          λ (_ , α) (_ , β) (_ , γ) → eq/ _ _ (cong √ (IdealAddAssoc _ _ _ _))

 ∨zComm : ∀ (𝔞 𝔟 : ZL) → 𝔞 ∨z 𝔟 ≡ 𝔟 ∨z 𝔞
 ∨zComm = SQ.elimProp2 (λ _ _ → squash/ _ _)
        λ (_ , α) (_ , β) → eq/ _ _
          (cong √ (FGIdealAddLemma _ α β ∙∙ +iComm _ _ ∙∙ sym (FGIdealAddLemma _ β α)))

 ∨zLid : ∀ (𝔞 : ZL) → 0z ∨z 𝔞 ≡ 𝔞
 ∨zLid = SQ.elimProp (λ _ → squash/ _ _) λ _ → eq/ _ _ refl

 ∨zRid : ∀ (𝔞 : ZL) → 𝔞 ∨z 0z ≡ 𝔞
 ∨zRid _ = ∨zComm _ _ ∙ ∨zLid _


 -- -- meet axioms
 ∧zAssoc : ∀ (𝔞 𝔟 𝔠 : ZL) → 𝔞 ∧z (𝔟 ∧z 𝔠) ≡ (𝔞 ∧z 𝔟) ∧z 𝔠
 ∧zAssoc = SQ.elimProp3 (λ _ _ _ → squash/ _ _)
    λ (_ , α) (_ , β) (_ , γ) → eq/ _ _
      (√ ⟨ α ··Fin (β ··Fin γ) ⟩     ≡⟨ cong √ (FGIdealMultLemma _ _ _) ⟩
       √ (⟨ α ⟩ ·i ⟨ β ··Fin γ ⟩)    ≡⟨ cong (λ x → √ (⟨ α ⟩ ·i x)) (FGIdealMultLemma _ _ _) ⟩
       √ (⟨ α ⟩ ·i (⟨ β ⟩ ·i ⟨ γ ⟩)) ≡⟨ cong √ (·iAssoc _ _ _) ⟩
       √ ((⟨ α ⟩ ·i ⟨ β ⟩) ·i ⟨ γ ⟩) ≡⟨ cong (λ x → √ (x ·i ⟨ γ ⟩)) (sym (FGIdealMultLemma _ _ _)) ⟩
       √ (⟨ α ··Fin β ⟩ ·i ⟨ γ ⟩)    ≡⟨ cong √ (sym (FGIdealMultLemma _ _ _)) ⟩
       √ ⟨ (α ··Fin β) ··Fin γ ⟩     ∎)

 ∧zComm : ∀ (𝔞 𝔟 : ZL) → 𝔞 ∧z 𝔟 ≡ 𝔟 ∧z 𝔞
 ∧zComm = SQ.elimProp2 (λ _ _ → squash/ _ _)
        λ (_ , α) (_ , β) → eq/ _ _
          (cong √ (FGIdealMultLemma _ α β ∙∙ ·iComm _ _ ∙∙ sym (FGIdealMultLemma _ β α)))

 ∧zRid : ∀ (𝔞 : ZL) → 𝔞 ∧z 1z ≡ 𝔞
 ∧zRid = SQ.elimProp (λ _ → squash/ _ _)
   λ (_ , α) → eq/ _ _ (cong √
     (⟨ α ··Fin (replicateFinVec 1 1r) ⟩ ≡⟨ FGIdealMultLemma _ _ _ ⟩
      ⟨ α ⟩ ·i ⟨ (replicateFinVec 1 1r) ⟩ ≡⟨ cong (⟨ α ⟩ ·i_) (contains1Is1 _ (indInIdeal _ _ zero)) ⟩
      ⟨ α ⟩ ·i 1Ideal                     ≡⟨ ·iRid _ ⟩
      ⟨ α ⟩ ∎))


 -- absorption and distributivity
 ∧zAbsorb∨z : ∀ (𝔞 𝔟 : ZL) → 𝔞 ∧z (𝔞 ∨z 𝔟) ≡ 𝔞
 ∧zAbsorb∨z = SQ.elimProp2 (λ _ _ → squash/ _ _)
            λ (_ , α) (_ , β) → eq/ _ _
              (√ ⟨ α ··Fin (α ++Fin β) ⟩     ≡⟨ cong √ (FGIdealMultLemma _ α (α ++Fin β)) ⟩
               √ (⟨ α ⟩ ·i ⟨ α ++Fin β ⟩)    ≡⟨ cong (λ x → √ (⟨ α ⟩ ·i x)) (FGIdealAddLemma _ α β) ⟩
               √ (⟨ α ⟩ ·i (⟨ α ⟩ +i ⟨ β ⟩)) ≡⟨ √·Absorb+ _ _ ⟩
               √ ⟨ α ⟩ ∎)

 ∧zLDist∨z : ∀ (𝔞 𝔟 𝔠 : ZL) → 𝔞 ∧z (𝔟 ∨z 𝔠) ≡ (𝔞 ∧z 𝔟) ∨z (𝔞 ∧z 𝔠)
 ∧zLDist∨z = SQ.elimProp3 (λ _ _ _ → squash/ _ _)
   λ (_ , α) (_ , β) (_ , γ) → eq/ _ _
     (√ ⟨ α ··Fin (β ++Fin γ) ⟩            ≡⟨ cong √ (FGIdealMultLemma _ _ _) ⟩
      √ (⟨ α ⟩ ·i ⟨ β ++Fin γ ⟩)           ≡⟨ cong (λ x → √ (⟨ α ⟩ ·i x)) (FGIdealAddLemma _ _ _) ⟩
      √ (⟨ α ⟩ ·i (⟨ β ⟩ +i ⟨ γ ⟩))        ≡⟨ cong √ (·iRdist+i _ _ _) ⟩
      -- L/R-dist are swapped
      -- in Lattices vs Rings
      √ (⟨ α ⟩ ·i ⟨ β ⟩ +i ⟨ α ⟩ ·i ⟨ γ ⟩) ≡⟨ cong₂ (λ x y → √ (x +i y))
                                                     (sym (FGIdealMultLemma _ _ _))
                                                     (sym (FGIdealMultLemma _ _ _)) ⟩
      √ (⟨ α ··Fin β ⟩ +i ⟨ α ··Fin γ ⟩)   ≡⟨ cong √ (sym (FGIdealAddLemma _ _ _)) ⟩
      √ ⟨ (α ··Fin β) ++Fin (α ··Fin γ) ⟩  ∎)


 ZariskiLattice : DistLattice (ℓ-suc ℓ)
 fst ZariskiLattice = ZL
 DistLatticeStr.0l (snd ZariskiLattice) = 0z
 DistLatticeStr.1l (snd ZariskiLattice) = 1z
 DistLatticeStr._∨l_ (snd ZariskiLattice) = _∨z_
 DistLatticeStr._∧l_ (snd ZariskiLattice) = _∧z_
 DistLatticeStr.isDistLattice (snd ZariskiLattice) =
   makeIsDistLattice∧lOver∨l squash/ ∨zAssoc ∨zRid ∨zComm
                                       ∧zAssoc ∧zRid ∧zComm ∧zAbsorb∨z ∧zLDist∨z



module _ (R' : CommRing ℓ) (L' : DistLattice ℓ') where

 open CommRingStr (R' .snd)
 open RingTheory (CommRing→Ring R')
 open Sum (CommRing→Ring R')
 open CommRingTheory R'
 open Exponentiation R'

 open DistLatticeStr (L' .snd) renaming (is-set to isSetL)
 open Join L'
 open LatticeTheory (DistLattice→Lattice L')
 open Order (DistLattice→Lattice L')
 open JoinSemilattice (Lattice→JoinSemilattice (DistLattice→Lattice L'))
 open PosetReasoning IndPoset
 open PosetStr (IndPoset .snd) hiding (_≤_)
 private
  R = fst R'
  L = fst L'

 record IsZarMap (d : R → L) : Type (ℓ-max ℓ ℓ') where
  constructor iszarmap

  field
   pres0 : d 0r ≡ 0l
   pres1 : d 1r ≡ 1l
   ·≡∧ : ∀ x y → d (x · y) ≡ d x ∧l d y
   +≤∨ : ∀ x y → d (x + y) ≤ d x ∨l d y

  ∑≤⋁ : {n : ℕ} (U : FinVec R n) → d (∑ U) ≤ ⋁ λ i → d (U i)
  ∑≤⋁ {n = zero} U = ∨lRid _ ∙ pres0
  ∑≤⋁ {n = suc n} U = d (∑ U)                        ≤⟨ ∨lIdem _ ⟩
                       d (U zero  + ∑ (U ∘ suc))     ≤⟨ +≤∨ _ _ ⟩
                       d (U zero) ∨l d (∑ (U ∘ suc)) ≤⟨ ≤-∨LPres _ _ _ (∑≤⋁ (U ∘ suc)) ⟩
                       d (U zero) ∨l ⋁ (d ∘ U ∘ suc) ≤⟨ ∨lIdem _ ⟩
                       ⋁ (d ∘ U) ◾

  d·LCancel : ∀ x y → d (x · y) ≤ d y
  d·LCancel x y = subst (λ a → a ≤ d y) (sym (·≡∧ x y)) (∧≤LCancelJoin _ _)

  linearCombination≤LCancel : {n : ℕ} (α β : FinVec R n)
                            → d (linearCombination R' α β) ≤ ⋁ (d ∘ β)
  linearCombination≤LCancel α β = is-trans _ _ _ (∑≤⋁ (λ i → α i · β i))
                                                 (≤-⋁Ext _ _ λ i → d·LCancel (α i) (β i))

  ZarMapIdem : ∀ (n : ℕ) (x : R) → d (x ^ (suc n)) ≡ d x
  ZarMapIdem zero x = ·≡∧ _ _ ∙∙ cong (d x ∧l_) pres1 ∙∙ ∧lRid _
  ZarMapIdem (suc n) x = ·≡∧ _ _ ∙∙ cong (d x ∧l_) (ZarMapIdem n x) ∙∙ ∧lIdem _

  ZarMapExpIneq : ∀ (n : ℕ) (x : R) → d x ≤ d (x ^ n)
  ZarMapExpIneq zero x = cong (d x ∨l_) pres1 ∙∙ 1lRightAnnihilates∨l _ ∙∙ sym pres1
  ZarMapExpIneq (suc n) x = subst (λ y → d x ≤ y) (sym (ZarMapIdem _ x)) (∨lIdem _)

  -- the crucial lemma about "Zariski maps"
  open CommIdeal R'
  open RadicalIdeal R'
  open isCommIdeal
  private
   ⟨_⟩ : {n : ℕ} → FinVec R n → CommIdeal
   ⟨ V ⟩ = ⟨ V ⟩[ R' ]

  ZarMapRadicalIneq : ∀ {n : ℕ} (α : FinVec R n) (x : R)
                    → x ∈ √ ⟨ α ⟩ → d x ≤ ⋁ (d ∘ α)
  ZarMapRadicalIneq α x = PT.elim (λ _ → isSetL _ _)
         (uncurry (λ n → (PT.elim (λ _ → isSetL _ _) (uncurry (curriedHelper n)))))
   where
   curriedHelper : (n : ℕ) (β : FinVec R _)
                 → x ^ n ≡ linearCombination R' β α → d x ≤ ⋁ (d ∘ α)
   curriedHelper n β xⁿ≡∑βα = d x ≤⟨ ZarMapExpIneq n x ⟩
                              d (x ^ n)
     ≤⟨ subst (λ y → y ≤ ⋁ (d ∘ α)) (sym (cong d xⁿ≡∑βα)) (linearCombination≤LCancel β α) ⟩
                              ⋁ (d ∘ α) ◾

module ZarLatUniversalProp (R' : CommRing ℓ) where
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

 open ZarLat R'
 open IsZarMap

 private
  R = fst R'
  ⟨_⟩ : {n : ℕ} → FinVec R n → CommIdeal
  ⟨ V ⟩ = ⟨ V ⟩[ R' ]


 D : R → ZL
 D x = [ 1 , replicateFinVec 1 x ] -- λ x → √⟨x⟩

 isZarMapD : IsZarMap R' ZariskiLattice D
 pres0 isZarMapD = eq/ _ _ (cong √ (0FGIdeal _ ∙ sym (emptyFGIdeal _ _)))
 pres1 isZarMapD = refl
 ·≡∧ isZarMapD x y = cong {B = λ _ → ZL} (λ U → [ 1 , U ]) (Length1··Fin x y)
 +≤∨ isZarMapD x y = eq/ _ _ (cong √ (CommIdeal≡Char (inclOfFGIdeal _ 3Vec ⟨ 2Vec ⟩ 3Vec⊆2Vec)
                                                       (inclOfFGIdeal _ 2Vec ⟨ 3Vec ⟩ 2Vec⊆3Vec)))
  where
  2Vec = replicateFinVec 1 x ++Fin replicateFinVec 1 y
  3Vec = replicateFinVec 1 (x + y) ++Fin (replicateFinVec 1 x ++Fin replicateFinVec 1 y)

  3Vec⊆2Vec : ∀ (i : Fin 3) → 3Vec i ∈ ⟨ 2Vec ⟩
  3Vec⊆2Vec zero = ⟨ 2Vec ⟩ .snd .+Closed (indInIdeal _ _ zero) (indInIdeal _ _ (suc zero))
  3Vec⊆2Vec (suc zero) = indInIdeal _ _ zero
  3Vec⊆2Vec (suc (suc zero)) = indInIdeal _ _ (suc zero)

  2Vec⊆3Vec : ∀ (i : Fin 2) → 2Vec i ∈ ⟨ 3Vec ⟩
  2Vec⊆3Vec zero = indInIdeal _ _ (suc zero)
  2Vec⊆3Vec (suc zero) = indInIdeal _ _ (suc (suc zero))


 -- defintion of the universal property
 hasZarLatUniversalProp : (L : DistLattice ℓ') (D : R → fst L)
                        → IsZarMap R' L D
                        → Type _
 hasZarLatUniversalProp {ℓ' = ℓ'} L D _ = ∀ (L' : DistLattice ℓ') (d : R → fst L')
                                       → IsZarMap R' L' d
                                       → ∃![ χ ∈ DistLatticeHom L L' ] (fst χ) ∘ D ≡ d

 isPropZarLatUniversalProp : (L : DistLattice ℓ') (D : R → fst L) (isZarMapD : IsZarMap R' L D)
                         → isProp (hasZarLatUniversalProp L D isZarMapD)
 isPropZarLatUniversalProp L D isZarMapD = isPropΠ3 (λ _ _ _ → isPropIsContr)

 ZLHasUniversalProp : hasZarLatUniversalProp ZariskiLattice D isZarMapD
 ZLHasUniversalProp L' d isZarMapd = (χ , funExt χcomp) , χunique
  where
  open DistLatticeStr (snd L') renaming (is-set to isSetL)
  open LatticeTheory (DistLattice→Lattice L')
  open Join L'
  open IsLatticeHom
  L = fst L'

  χ : DistLatticeHom ZariskiLattice L'
  fst χ = SQ.rec isSetL (λ (_ , α) → ⋁ (d ∘ α))
                         λ (_ , α) (_ , β) → curriedHelper α β
   where
   curriedHelper : {n m : ℕ} (α : FinVec R n) (β : FinVec R m)
                 → √ ⟨ α ⟩ ≡ √ ⟨ β ⟩ → ⋁ (d ∘ α) ≡ ⋁ (d ∘ β)
   curriedHelper α β √⟨α⟩≡√⟨β⟩ = is-antisym _ _ ineq1 ineq2
    where
    open Order (DistLattice→Lattice L')
    open JoinSemilattice (Lattice→JoinSemilattice (DistLattice→Lattice L'))
    open PosetReasoning IndPoset
    open PosetStr (IndPoset .snd) hiding (_≤_)

    incl1 : √ ⟨ α ⟩ ⊆ √ ⟨ β ⟩
    incl1 = ⊆-refl-consequence _ _ (cong fst √⟨α⟩≡√⟨β⟩) .fst

    ineq1 : ⋁ (d ∘ α) ≤ ⋁ (d ∘ β)
    ineq1 = ⋁IsMax (d ∘ α) (⋁ (d ∘ β))
            λ i → ZarMapRadicalIneq isZarMapd β (α i) (√FGIdealCharLImpl α ⟨ β ⟩ incl1 i)

    incl2 : √ ⟨ β ⟩ ⊆ √ ⟨ α ⟩
    incl2 = ⊆-refl-consequence _ _ (cong fst √⟨α⟩≡√⟨β⟩) .snd

    ineq2 : ⋁ (d ∘ β) ≤ ⋁ (d ∘ α)
    ineq2 = ⋁IsMax (d ∘ β) (⋁ (d ∘ α))
            λ i → ZarMapRadicalIneq isZarMapd α (β i) (√FGIdealCharLImpl β ⟨ α ⟩ incl2 i)


  pres0 (snd χ) = refl
  pres1 (snd χ) = ∨lRid _ ∙ isZarMapd .pres1
  pres∨l (snd χ) = elimProp2 (λ _ _ → isSetL _ _) (uncurry (λ n α → uncurry (curriedHelper n α)))
   where
   curriedHelper : (n : ℕ) (α : FinVec R n) (m : ℕ) (β : FinVec R m)
                 → ⋁ (d ∘ (α ++Fin β)) ≡ ⋁ (d ∘ α) ∨l ⋁ (d ∘ β)
   curriedHelper zero α _ β = sym (∨lLid _)
   curriedHelper (suc n) α _ β =
                   ⋁ (d ∘ (α ++Fin β)) ≡⟨ refl ⟩
                   d (α zero) ∨l ⋁ (d ∘ ((α ∘ suc) ++Fin β))

                  ≡⟨ cong (d (α zero) ∨l_) (curriedHelper _ (α ∘ suc) _ β) ⟩

                   d (α zero) ∨l (⋁ (d ∘ α ∘ suc) ∨l ⋁ (d ∘ β))
                  ≡⟨ ∨lAssoc _ _ _ ⟩

                   ⋁ (d ∘ α) ∨l ⋁ (d ∘ β) ∎

  pres∧l (snd χ) = elimProp2 (λ _ _ → isSetL _ _) (uncurry (λ n α → uncurry (curriedHelper n α)))
   where
   -- have to repeat this one here so the termination checker won't complain
   oldHelper : (n : ℕ) (α : FinVec R n) (m : ℕ) (β : FinVec R m)
             → ⋁ (d ∘ (α ++Fin β)) ≡ ⋁ (d ∘ α) ∨l ⋁ (d ∘ β)
   oldHelper zero α _ β = sym (∨lLid _)
   oldHelper (suc n) α _ β = cong (d (α zero) ∨l_) (oldHelper _ (α ∘ suc) _ β) ∙ ∨lAssoc _ _ _

   curriedHelper : (n : ℕ) (α : FinVec R n) (m : ℕ) (β : FinVec R m)
                 → ⋁ (d ∘ (α ··Fin β)) ≡ ⋁ (d ∘ α) ∧l ⋁ (d ∘ β)
   curriedHelper zero α _ β = sym (0lLeftAnnihilates∧l _)
   curriedHelper (suc n) α _ β =
      ⋁ (d ∘ (α ··Fin β)) ≡⟨ refl ⟩
      ⋁ (d ∘ ((λ j → α zero · β j) ++Fin ((α ∘ suc) ··Fin β)))

     ≡⟨ oldHelper _ (λ j → α zero · β j) _ ((α ∘ suc) ··Fin β) ⟩

      ⋁ (d ∘ (λ j → α zero · β j)) ∨l ⋁ (d ∘ ((α ∘ suc) ··Fin β))

     ≡⟨ cong (_∨l ⋁ (d ∘ ((α ∘ suc) ··Fin β))) (⋁Ext (λ j → isZarMapd .·≡∧ (α zero) (β j))) ⟩

      ⋁ (λ j → d (α zero) ∧l d (β j)) ∨l ⋁ (d ∘ ((α ∘ suc) ··Fin β))

     ≡⟨ cong (_∨l ⋁ (d ∘ ((α ∘ suc) ··Fin β))) (sym (⋁Meetrdist _ _)) ⟩

      (d (α zero) ∧l ⋁ (d ∘ β)) ∨l ⋁ (d ∘ ((α ∘ suc) ··Fin β))

     ≡⟨ cong ((d (α zero) ∧l ⋁ (d ∘ β)) ∨l_) (curriedHelper _ (α ∘ suc) _ β) ⟩

      (d (α zero) ∧l ⋁ (d ∘ β)) ∨l (⋁ (d ∘ α ∘ suc) ∧l ⋁ (d ∘ β))

     ≡⟨ sym (∧lRdist∨l _ _ _) ⟩

      ⋁ (d ∘ α) ∧l ⋁ (d ∘ β) ∎


  χcomp : ∀ (f : R) → χ .fst (D f) ≡ d f
  χcomp f = ∨lRid (d f)

  χunique : (y : Σ[ χ' ∈ DistLatticeHom ZariskiLattice L' ] fst χ' ∘ D ≡ d)
          → (χ , funExt χcomp) ≡ y
  χunique (χ' , χ'∘D≡d) = Σ≡Prop (λ _ → isSetΠ (λ _ → isSetL) _ _) (LatticeHom≡f _ _
                                 (funExt (elimProp (λ _ → isSetL _ _) (uncurry uniqHelper))))
   where
   uniqHelper : (n : ℕ) (α : FinVec R n) → fst χ [ n , α ] ≡ fst χ' [ n , α ]
   uniqHelper zero _ = sym (cong (λ α → fst χ' [ 0 , α ]) (funExt (λ ())) ∙ χ' .snd .pres0)
   uniqHelper (suc n) α =
       ⋁ (d ∘ α) ≡⟨ refl ⟩
       d (α zero) ∨l ⋁ (d ∘ α ∘ suc)

      ≡⟨ cong (d (α zero) ∨l_) (uniqHelper n (α ∘ suc)) ⟩ -- the inductive step

       d (α zero) ∨l fst χ' [ n , α ∘ suc ]

      ≡⟨ cong (_∨l fst χ' [ n , α ∘ suc ]) (sym (funExt⁻ χ'∘D≡d (α zero))) ⟩

       fst χ' (D (α zero)) ∨l fst χ' [ n , α ∘ suc ]

      ≡⟨ sym (χ' .snd .pres∨l _ _) ⟩

       fst χ' (D (α zero) ∨z [ n , α ∘ suc ])

      ≡⟨ cong (λ β → fst χ' [ suc n , β ]) (funExt (λ { zero → refl ; (suc i) → refl })) ⟩

       fst χ' [ suc n , α ] ∎


 -- the map induced by applying the universal property to the Zariski lattice
 -- itself is the identity hom
 ZLUniversalPropCorollary : ZLHasUniversalProp ZariskiLattice D isZarMapD .fst .fst
                          ≡ idDistLatticeHom ZariskiLattice
 ZLUniversalPropCorollary = cong fst
                              (ZLHasUniversalProp ZariskiLattice D isZarMapD .snd
                                 (idDistLatticeHom ZariskiLattice , refl))


-- An equivalent definition that doesn't bump up the unviverse level
module SmallZarLat (R' : CommRing ℓ) where
 open CommRingStr (snd R')
 open CommIdeal R'
 open RadicalIdeal R'
 open ZarLat R'

 open Iso

 private
  R = fst R'
  A = Σ[ n ∈ ℕ ] (FinVec R n)
  ⟨_⟩ : {n : ℕ} → FinVec R n → CommIdeal
  ⟨ V ⟩ = ⟨ V ⟩[ R' ]
  -- This is small!
  _≼_ : A → A → Type ℓ
  (_ , α) ≼ (_ , β) = ∀ i → α i ∈ √ ⟨ β ⟩

 _∼'_ :  A → A → Type ℓ
 α ∼' β = (α ≼ β) × (β ≼ α)

 -- lives in the same universe as R
 ZL' : Type ℓ
 ZL' = A / (_∼'_)


 IsoLarLatSmall : Iso ZL ZL'
 IsoLarLatSmall = relBiimpl→TruncIso ~→∼' ~'→∼
  where
  ~→∼' : ∀ {a b : A} → a ∼ b → a ∼' b
  ~→∼' r = √FGIdealCharLImpl _ ⟨ _ ⟩ (λ x h → subst (λ p → x ∈ p) r h)
         , √FGIdealCharLImpl _ ⟨ _ ⟩ (λ x h → subst (λ p → x ∈ p) (sym r) h)

  ~'→∼ : ∀ {a b : A} → a ∼' b → a ∼ b
  ~'→∼ r = CommIdeal≡Char (√FGIdealCharRImpl _ ⟨ _ ⟩ (fst r))
                          (√FGIdealCharRImpl _ ⟨ _ ⟩ (snd r))

 ZL≃ZL' : ZL ≃ ZL'
 ZL≃ZL' = isoToEquiv IsoLarLatSmall


module BasicOpens (R' : CommRing ℓ) where
 open CommRingStr ⦃...⦄
 open RingTheory (CommRing→Ring R')
 open CommIdeal R'
 open isCommIdeal

 open ZarLat R'
 open ZarLatUniversalProp R'
 open IsZarMap

 open Join ZariskiLattice
 open JoinSemilattice (Lattice→JoinSemilattice (DistLattice→Lattice ZariskiLattice))
 open IsBasis

 private
  R = fst R'
  instance
   _ = snd R'
  ⟨_⟩ : {n : ℕ} → FinVec R n → CommIdeal
  ⟨ V ⟩ = ⟨ V ⟩[ R' ]


 BasicOpens : ℙ ZL
 BasicOpens 𝔞 = (∃[ f ∈ R ] (D f ≡ 𝔞)) , isPropPropTrunc

 BO : Type (ℓ-suc ℓ)
 BO = Σ[ 𝔞 ∈ ZL ] (𝔞 ∈ₚ BasicOpens)

 basicOpensAreBasis : IsBasis ZariskiLattice BasicOpens
 contains1 basicOpensAreBasis = ∣ 1r , isZarMapD .pres1 ∣
 ∧lClosed basicOpensAreBasis 𝔞 𝔟 = map2
            λ (f , Df≡𝔞) (g , Dg≡𝔟) → (f · g) , isZarMapD .·≡∧ f g ∙ cong₂ (_∧z_) Df≡𝔞 Dg≡𝔟
 ⋁Basis basicOpensAreBasis = elimProp (λ _ → isPropPropTrunc) Σhelper
  where
  Σhelper : (a : Σ[ n ∈ ℕ ] FinVec R n)
          → ∃[ n ∈ ℕ ] Σ[ α ∈ FinVec ZL n ] (∀ i → α i ∈ₚ BasicOpens) × (⋁ α ≡ [ a ])
  Σhelper (n , α) = ∣ n , (D ∘ α) , (λ i → ∣ α i , refl ∣) , path ∣
   where
   path : ⋁ (D ∘ α) ≡ [ n , α ]
   path = funExt⁻ (cong fst ZLUniversalPropCorollary) _


 -- The structure presheaf on BO
 ZariskiCat = DistLatticeCategory ZariskiLattice

 BOCat : Category (ℓ-suc ℓ) (ℓ-suc ℓ)
 BOCat = ΣPropCat ZariskiCat BasicOpens

 private
  P : ZL → Type _
  P 𝔞 = Σ[ f ∈ R ] (D f ≡ 𝔞) -- the untruncated defining property

  𝓕 : Σ ZL P → CommAlgebra R' _
  𝓕 (_ , f , _) = R[1/ f ]AsCommAlgebra -- D(f) ↦ R[1/f]

  uniqueHom : ∀ (x y : Σ ZL P) → (fst x) ≤ (fst y) → isContr (CommAlgebraHom (𝓕 y) (𝓕 x))
  uniqueHom (𝔞 , f , p) (𝔟 , g , q) = contrHoms 𝔞 𝔟 f g p q
   where
   open InvertingElementsBase R'

   contrHoms : (𝔞 𝔟 : ZL) (f g : R) (p : D f ≡ 𝔞) (q : D g ≡ 𝔟)
             → 𝔞 ≤ 𝔟 → isContr (CommAlgebraHom R[1/ g ]AsCommAlgebra R[1/ f ]AsCommAlgebra)
   contrHoms 𝔞 𝔟 f g p q 𝔞≤𝔟 = R[1/g]HasAlgUniversalProp R[1/ f ]AsCommAlgebra
     λ s s∈[gⁿ|n≥0] → subst-∈ₚ (R[1/ f ]AsCommRing ˣ)
       (sym (·Rid (s /1))) --can't apply the lemma directly as we get mult with 1 somewhere
         (RadicalLemma.toUnit R' f g f∈√⟨g⟩ s s∈[gⁿ|n≥0])
    where
    open AlgLoc R' [ g ⁿ|n≥0] (powersFormMultClosedSubset g)
         renaming (S⁻¹RHasAlgUniversalProp to R[1/g]HasAlgUniversalProp)
    open S⁻¹RUniversalProp R' [ f ⁿ|n≥0] (powersFormMultClosedSubset f) using (_/1)
    open RadicalIdeal R'

    private
     instance
      _ = snd R[1/ f ]AsCommRing

    Df≤Dg : D f ≤ D g
    Df≤Dg = subst2 _≤_ (sym p) (sym q) 𝔞≤𝔟

    radicalHelper : √ ⟨ replicateFinVec 1 f ++Fin replicateFinVec 1 g ⟩
                  ≡ √ ⟨ replicateFinVec 1 g ⟩
    radicalHelper =
      isEquivRel→effectiveIso (λ _ _ → isSetCommIdeal _ _) ∼EquivRel _ _ .fun Df≤Dg

    f∈√⟨g⟩ : f ∈ √ ⟨ replicateFinVec 1 g ⟩
    f∈√⟨g⟩ = subst (f ∈_) radicalHelper (∈→∈√ _ _ (indInIdeal _ _ zero))


 open PreSheafFromUniversalProp ZariskiCat P 𝓕 uniqueHom
 BasisStructurePShf : Functor (BOCat ^op) (CommAlgebrasCategory R')
 BasisStructurePShf = universalPShf


 -- now prove the sheaf properties
 open SheafOnBasis ZariskiLattice (CommAlgebrasCategory R' {ℓ' = ℓ})
                   (TerminalCommAlgebra R') BasicOpens basicOpensAreBasis

 isSheafBasisStructurePShf : isDLBasisSheaf BasisStructurePShf
 fst isSheafBasisStructurePShf 0∈BO =
   transport (λ i → F-ob (0z , canonical0∈BO≡0∈BO i) ≡ UnitCommAlgebra R') R[1/0]≡0
   where
   open Functor ⦃...⦄
   instance
    _ = BasisStructurePShf

   canonical0∈BO : 0z ∈ₚ BasicOpens
   canonical0∈BO = ∣ 0r , isZarMapD .pres0 ∣

   canonical0∈BO≡0∈BO : canonical0∈BO ≡ 0∈BO
   canonical0∈BO≡0∈BO = BasicOpens 0z .snd _ _

   R[1/0]≡0 : R[1/ 0r ]AsCommAlgebra ≡ UnitCommAlgebra R'
   R[1/0]≡0 = uaCommAlgebra (e , eIsRHom)
    where
    open InvertingElementsBase R' using (isContrR[1/0])
    open IsAlgebraHom

    e : R[1/ 0r ]AsCommAlgebra .fst ≃ UnitCommAlgebra R' .fst
    e = isContr→Equiv isContrR[1/0] isContrUnit*

    eIsRHom : IsCommAlgebraEquiv (R[1/ 0r ]AsCommAlgebra .snd) e (UnitCommAlgebra R' .snd)
    pres0 eIsRHom = refl
    pres1 eIsRHom = refl
    pres+ eIsRHom _ _ = refl
    pres· eIsRHom _ _ = refl
    pres- eIsRHom _ = refl
    pres⋆ eIsRHom _ _ = refl

 snd isSheafBasisStructurePShf (𝔞 , 𝔞∈BO) (𝔟 , 𝔟∈BO) 𝔞∨𝔟∈BO = curriedHelper 𝔞 𝔟 𝔞∈BO 𝔟∈BO 𝔞∨𝔟∈BO
  where
  open condSquare
  {-
     here:
     BFsq (𝔞 , 𝔞∈BO) (𝔟 , 𝔟∈BO) 𝔞∨𝔟∈BO BasisStructurePShf =

     𝓞 (𝔞∨𝔟) → 𝓞 (𝔞)

       ↓         ↓

     𝓞 (𝔟)  →  𝓞 (𝔞∧𝔟)

  -}
  curriedHelper : (𝔞 𝔟 : ZL) (𝔞∈BO : 𝔞 ∈ₚ BasicOpens) (𝔟∈BO : 𝔟 ∈ₚ BasicOpens)
                  (𝔞∨𝔟∈BO : 𝔞 ∨z 𝔟 ∈ₚ BasicOpens)
                → isPullback (CommAlgebrasCategory R') _ _ _
                             (BFsq (𝔞 , 𝔞∈BO) (𝔟 , 𝔟∈BO) 𝔞∨𝔟∈BO BasisStructurePShf)
  curriedHelper 𝔞 𝔟 = elim3 (λ 𝔞∈BO 𝔟∈BO 𝔞∨𝔟∈BO → isPropIsPullback _ _ _ _
                            (BFsq (𝔞 , 𝔞∈BO) (𝔟 , 𝔟∈BO) 𝔞∨𝔟∈BO BasisStructurePShf))
                            Σhelper
   where
   Σhelper : (a : Σ[ f ∈ R ] D f ≡ 𝔞) (b : Σ[ g ∈ R ] D g ≡ 𝔟) (c : Σ[ h ∈ R ] D h ≡ 𝔞 ∨z 𝔟)
           → isPullback (CommAlgebrasCategory R') _ _ _
                        (BFsq (𝔞 , ∣ a ∣) (𝔟 , ∣ b ∣) ∣ c ∣ BasisStructurePShf)
   Σhelper (f , Df≡𝔞) (g , Dg≡𝔟) (h , Dh≡𝔞∨𝔟) = {!toSheaf.lemma (Bsq (𝔞 , ∣ f , Df≡𝔞 ∣) (𝔟 , ∣ g , Dg≡𝔟 ∣) ∣ h , Dh≡𝔞∨𝔟 ∣) theAlgebraCospan theAlgebraPullback refl ? ? ?!}
   {-
     write down ideal facts implied by √⟨h⟩≡√⟨f,g⟩
     get pullbacksquare in CommRings (over R[1/h])
     use PullbackFromCommRing
     use toSheaf.lemma
   -}
    where
    open Exponentiation R'
    open RadicalIdeal R'
    open InvertingElementsBase R'
    open DoubleLoc R' h
    --open Loc R' [ h ⁿ|n≥0] (powersFormMultClosedSubset h)
    open S⁻¹RUniversalProp R' [ h ⁿ|n≥0] (powersFormMultClosedSubset h)
    open CommIdeal R[1/ h ]AsCommRing using () renaming (CommIdeal to CommIdealₕ ; _∈_ to _∈ₕ_)
    --open RadicalIdeal R[1/ h ]AsCommRing using () renaming (√ to √ₕ)

    instance
     _ = snd R[1/ h ]AsCommRing

    ⟨_⟩ₕ : {n : ℕ} → FinVec R[1/ h ] n → CommIdealₕ
    ⟨ V ⟩ₕ = ⟨ V ⟩[ R[1/ h ]AsCommRing ]

    radicalPath : √ ⟨ replicateFinVec 1 h ⟩ ≡ √ ⟨ replicateFinVec 1 f ++Fin replicateFinVec 1 g ⟩
    radicalPath = isEquivRel→effectiveIso (λ _ _ → isSetCommIdeal _ _) ∼EquivRel _ _ .fun DHelper
     where
     DHelper : D h ≡ D f ∨z D g
     DHelper = Dh≡𝔞∨𝔟 ∙ cong₂ (_∨z_) (sym Df≡𝔞) (sym Dg≡𝔟)

    1∈Radical : 1r ∈ₕ ⟨ replicateFinVec 1 (f /1) ++Fin replicateFinVec 1 (g /1) ⟩ₕ
    1∈Radical = helper1 (subst (h ∈_) radicalPath (∈→∈√ _ _ (indInIdeal _ _ zero)))
     where
     helper1 : h ∈ √ ⟨ replicateFinVec 1 f ++Fin replicateFinVec 1 g ⟩
             → 1r ∈ₕ ⟨ replicateFinVec 1 (f /1) ++Fin replicateFinVec 1 (g /1) ⟩ₕ
     helper1 = PT.rec isPropPropTrunc (uncurry helper2)
      where
      helper2 : (n : ℕ)
              → h ^ n ∈ ⟨ replicateFinVec 1 f ++Fin replicateFinVec 1 g ⟩
              → 1r ∈ₕ ⟨ replicateFinVec 1 (f /1) ++Fin replicateFinVec 1 (g /1) ⟩ₕ
      helper2 n = map helper3
       where
       helper3 : Σ[ α ∈ FinVec R 2 ]
                  h ^ n ≡ linearCombination R' α (replicateFinVec 1 f ++Fin replicateFinVec 1 g)
               → Σ[ β ∈ FinVec R[1/ h ] 2 ]
                  1r ≡ linearCombination R[1/ h ]AsCommRing β
                                         (replicateFinVec 1 (f /1) ++Fin replicateFinVec 1 (g /1))
       helper3 (α , p) = β , path
        where
        β : FinVec R[1/ h ] 2
        β zero = [ α zero , h ^ n , ∣ n , refl ∣ ]
        β (suc zero) = [ α (suc zero) , h ^ n , ∣ n , refl ∣ ]

        path : 1r ≡ linearCombination R[1/ h ]AsCommRing β
                                      (replicateFinVec 1 (f /1) ++Fin replicateFinVec 1 (g /1))
        path = eq/ _ _ ((1r , ∣ 0 , refl ∣) , bigPath)
             ∙ cong (β zero · (f /1) +_) (sym (+Rid (β (suc zero) · (g /1))))
         where
         useSolver1 : ∀ hn → 1r · 1r · ((hn · 1r) · (hn · 1r)) ≡ hn · hn
         useSolver1 = solve R'

         useSolver2 : ∀ az f hn as g → hn · (az · f + (as · g + 0r))
                                      ≡ 1r · (az · f · (hn · 1r) + as · g · (hn · 1r)) · 1r
         useSolver2 = solve R'

         bigPath : 1r · 1r · ((h ^ n · 1r) · (h ^ n · 1r))
                 ≡ 1r · (α zero · f · (h ^ n · 1r) + α (suc zero) · g · (h ^ n · 1r)) · 1r
         bigPath = useSolver1 (h ^ n) ∙ cong (h ^ n ·_) p ∙ useSolver2 _ _ _ _ _

    -- we get a pullback square in comm rings that then gives us the desired
    -- square in R-algebras that we want to transport
    theRingCospan = fgCospan R[1/ h ]AsCommRing (f /1) (g /1)
    theRingPBSquare = fgPullback R[1/ h ]AsCommRing (f /1) (g /1) 1∈Radical

    R[1/h][1/fg] = InvertingElementsBase.R[1/_] R[1/ h ]AsCommRing ((f /1) · (g /1))
    R[1/h][1/fg]AsCommRing = InvertingElementsBase.R[1/_]AsCommRing
                               R[1/ h ]AsCommRing ((f /1) · (g /1))

    open IsRingHom
    /1/1AsCommRingHomFG : CommRingHom R' R[1/h][1/fg]AsCommRing
    fst /1/1AsCommRingHomFG r = [ [ r , 1r , ∣ 0 , refl ∣ ] , 1r , ∣ 0 , refl ∣ ]
    pres0 (snd /1/1AsCommRingHomFG) = refl
    pres1 (snd /1/1AsCommRingHomFG) = refl
    pres+ (snd /1/1AsCommRingHomFG) x y = {!!}
      -- cong [_] (≡-× (cong [_] (≡-× (cong₂ _+_ (sym {!!}) {!!}) {!!})) {!!})
    pres· (snd /1/1AsCommRingHomFG) x y = cong [_] (≡-× (cong [_] (≡-× refl
                                            (Σ≡Prop (λ _ → isPropPropTrunc) (sym (·Rid 1r)))))
                                            (Σ≡Prop (λ _ → isPropPropTrunc) (sym (·Rid 1r))))
    pres- (snd /1/1AsCommRingHomFG) x = refl

    --isRHomR[1/h]→R[1/h][1/f]

    open PullbackFromCommRing R' theRingCospan theRingPBSquare
         /1AsCommRingHom (/1/1AsCommRingHom g) (/1/1AsCommRingHom f) /1/1AsCommRingHomFG
    -- theAlgebraCospan = algCospan {!!} {!!} {!!} {!!}
    -- theAlgebraPullback = algPullback {!!} {!!} {!!} {!!}

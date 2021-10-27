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
open import Cubical.Algebra.DistLattice.BigOps
open import Cubical.Algebra.Matrix

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
 1z = [ 1 , (replicateFinVec 1 1r) ]

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
        λ (_ , α) (_ , β) → eq/ _ _
          (cong √i (FGIdealAddLemma _ α β ∙∙ +iComm _ _ ∙∙ sym (FGIdealAddLemma _ β α)))

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
        λ (_ , α) (_ , β) → eq/ _ _
          (cong √i (FGIdealMultLemma _ α β ∙∙ ·iComm _ _ ∙∙ sym (FGIdealMultLemma _ β α)))


 -- ∧zLid : ∀ (𝔞 : ZL) → 1z ∧z 𝔞 ≡ 𝔞
 -- ∧zLid = SQ.elimProp (λ _ → squash/ _ _) λ (_ , α) → {!!} --eq/ _ _ {!!}


 ∧zRid : ∀ (𝔞 : ZL) → 𝔞 ∧z 1z ≡ 𝔞
 ∧zRid = SQ.elimProp (λ _ → squash/ _ _)
   λ (_ , α) → eq/ _ _ (cong √i
     (⟨ α ··Fin (replicateFinVec 1 1r) ⟩ ≡⟨ FGIdealMultLemma _ _ _ ⟩
      ⟨ α ⟩ ·i ⟨ (replicateFinVec 1 1r) ⟩ ≡⟨ cong (⟨ α ⟩ ·i_) (contains1Is1 _ (indInIdeal _ _ zero)) ⟩
      ⟨ α ⟩ ·i 1Ideal                     ≡⟨ ·iRid _ ⟩
      ⟨ α ⟩ ∎))


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
      √i (⟨ α ⟩ ·i (⟨ β ⟩ +i ⟨ γ ⟩))        ≡⟨ cong √i (·iRdist+i _ _ _) ⟩
      -- L/R-dist are swapped
      -- in Lattices vs Rings
      √i (⟨ α ⟩ ·i ⟨ β ⟩ +i ⟨ α ⟩ ·i ⟨ γ ⟩) ≡⟨ cong₂ (λ x y → √i (x +i y))
                                                     (sym (FGIdealMultLemma _ _ _))
                                                     (sym (FGIdealMultLemma _ _ _)) ⟩
      √i (⟨ α ··Fin β ⟩ +i ⟨ α ··Fin γ ⟩)   ≡⟨ cong √i (sym (FGIdealAddLemma _ _ _)) ⟩
      √i ⟨ (α ··Fin β) ++Fin (α ··Fin γ) ⟩  ∎)


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

 open DistLatticeStr (L' .snd)
 open Join L'
 open JoinSemilattice (Lattice→JoinSemilattice (DistLattice→Lattice L'))
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

  -- ∑≤⋁ : {n : ℕ} (U : FinVec R n) → d (∑ U) ≤ ⋁ λ i → d (U i)
  -- ∑≤⋁ {n = zero} U = ∨lRid _ ∙ pres0
  -- ∑≤⋁ {n = suc n} U = is-trans _ _ _ (+≤∨ (U zero) (∑ (U ∘ suc))) {!!}
  --  where
  --  open IsPoset ⦃...⦄
  --  instance _ = IndPoset .snd .PosetStr.isPoset


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
 pres0 isZarMapD = eq/ _ _ (cong √i (0FGIdeal _ ∙ sym (emptyFGIdeal _ _)))
 pres1 isZarMapD = refl
 ·≡∧ isZarMapD x y = cong {B = λ _ → ZL} (λ U → [ 1 , U ]) (Length1··Fin x y)
 +≤∨ isZarMapD x y = eq/ _ _ (cong √i (CommIdeal≡Char (inclOfFGIdeal _ 3Vec ⟨ 2Vec ⟩ 3Vec⊆2Vec)
                                                       (inclOfFGIdeal _ 2Vec ⟨ 3Vec ⟩ 2Vec⊆3Vec)))
  where
  2Vec = replicateFinVec 1 x ++Fin replicateFinVec 1 y
  3Vec = replicateFinVec 1 (x + y) ++Fin (replicateFinVec 1 x ++Fin replicateFinVec 1 y)

  3Vec⊆2Vec : ∀ (i : Fin 3) → 3Vec i ∈ ⟨ 2Vec ⟩ .fst
  3Vec⊆2Vec zero = ⟨ 2Vec ⟩ .snd .+Closed (indInIdeal _ _ zero) (indInIdeal _ _ (suc zero))
  3Vec⊆2Vec (suc zero) = indInIdeal _ _ zero
  3Vec⊆2Vec (suc (suc zero)) = indInIdeal _ _ (suc zero)

  2Vec⊆3Vec : ∀ (i : Fin 2) → 2Vec i ∈ ⟨ 3Vec ⟩ .fst
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
  open Join L'
  open IsLatticeHom
  L = fst L'

  χ : DistLatticeHom ZariskiLattice L'
  fst χ = SQ.rec isSetL (λ (_ , α) → ⋁ (d ∘ α))
        {!!} -- the big sanity check: If √⟨α⟩≡√⟨β⟩ then ⋁dα≡⋁dβ
  pres0 (snd χ) = refl
  pres1 (snd χ) = ∨lRid _ ∙ isZarMapd .pres1
  pres∨l (snd χ) = elimProp2 (λ _ _ → isSetL _ _) {!!} -- this is hard
  pres∧l (snd χ) = elimProp2 (λ _ _ → isSetL _ _) {!!} -- this is even harder

  χcomp : ∀ (f : R) → χ .fst (D f) ≡ d f
  χcomp f = ∨lRid (d f)

  χunique : (y : Σ[ χ' ∈ DistLatticeHom ZariskiLattice L' ] fst χ' ∘ D ≡ d)
          → (χ , funExt χcomp) ≡ y
  χunique (χ' , χ'∘D≡d) = Σ≡Prop (λ _ → isSetΠ (λ _ → isSetL) _ _) (LatticeHom≡f _ _
                                 (funExt (elimProp (λ _ → isSetL _ _) (uncurry uniqHelper))))
   where
   uniqHelper : (n : ℕ) (α : FinVec R n) → fst χ [ n , α ] ≡ fst χ' [ n , α ]
   uniqHelper zero α = {!!}
   uniqHelper (suc n) α =
    ⋁ (d ∘ α) ≡⟨ refl ⟩
    d (α zero) ∨l ⋁ (d ∘ α ∘ suc) ≡⟨ cong (d (α zero) ∨l_) (uniqHelper n (α ∘ suc)) ⟩
    d (α zero) ∨l fst χ' [ n , α ∘ suc ] ≡⟨ {!!} ⟩
    fst χ' (D (α zero) ∨z [ n , α ∘ suc ]) ≡⟨ cong (fst χ') {!refl!} ⟩
    fst χ' [ suc n , α ] ∎

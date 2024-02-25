{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Algebra.ZariskiLattice.UniversalProperty where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Powerset using (ℙ ; ⊆-refl-consequence)

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
open import Cubical.Algebra.Semilattice
open import Cubical.Algebra.Lattice
open import Cubical.Algebra.DistLattice
open import Cubical.Algebra.DistLattice.Basis
open import Cubical.Algebra.DistLattice.BigOps
open import Cubical.Algebra.Matrix

open import Cubical.Algebra.ZariskiLattice.Base

open import Cubical.HITs.SetQuotients as SQ
open import Cubical.HITs.PropositionalTruncation as PT

private
  variable
    ℓ ℓ' : Level


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
 pres0 isZarMapD = eq/ _ _ (≡→∼ (cong √ (0FGIdeal _ ∙ sym (emptyFGIdeal _ _))))
 pres1 isZarMapD = refl
 ·≡∧ isZarMapD x y = cong {B = λ _ → ZL} (λ U → [ 1 , U ]) (Length1··Fin x y)
 +≤∨ isZarMapD x y = eq/ _ _ (≡→∼ (cong √ (CommIdeal≡Char
                                           (inclOfFGIdeal _ 3Vec ⟨ 2Vec ⟩ 3Vec⊆2Vec)
                                           (inclOfFGIdeal _ 2Vec ⟨ 3Vec ⟩ 2Vec⊆3Vec))))
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
                 → (n , α) ∼ (m , β) → ⋁ (d ∘ α) ≡ ⋁ (d ∘ β)
   curriedHelper α β α∼β = is-antisym _ _ ineq1 ineq2
    where
    open Order (DistLattice→Lattice L')
    open JoinSemilattice (Lattice→JoinSemilattice (DistLattice→Lattice L'))
    open PosetReasoning IndPoset
    open PosetStr (IndPoset .snd) hiding (_≤_)

    incl1 : √ ⟨ α ⟩ ⊆ √ ⟨ β ⟩
    incl1 = ⊆-refl-consequence _ _ (cong fst (∼→≡ α∼β)) .fst

    ineq1 : ⋁ (d ∘ α) ≤ ⋁ (d ∘ β)
    ineq1 = ⋁IsMax (d ∘ α) (⋁ (d ∘ β))
            λ i → ZarMapRadicalIneq isZarMapd β (α i) (√FGIdealCharLImpl α ⟨ β ⟩ incl1 i)

    incl2 : √ ⟨ β ⟩ ⊆ √ ⟨ α ⟩
    incl2 = ⊆-refl-consequence _ _ (cong fst (∼→≡ α∼β)) .snd

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

 -- and another corollary
 module _ where
  open Join ZariskiLattice
  ⋁D≡ : {n : ℕ} (α : FinVec R n) → ⋁ (D ∘ α) ≡ [ n , α ]
  ⋁D≡ _ = funExt⁻ (cong fst ZLUniversalPropCorollary) _

-- the lattice morphism induced by a ring morphism
module _ {A B : CommRing ℓ} (φ : CommRingHom A B) where

 open ZarLat
 open ZarLatUniversalProp
 open IsZarMap
 open CommRingStr ⦃...⦄
 open DistLatticeStr ⦃...⦄
 open IsRingHom
 private
   instance
     _ = A .snd
     _ = B .snd
     _ = (ZariskiLattice A) .snd
     _ = (ZariskiLattice B) .snd

 Dcomp : A .fst → ZL B
 Dcomp f = D B (φ .fst f)

 isZarMapDcomp : IsZarMap A (ZariskiLattice B) Dcomp
 pres0 isZarMapDcomp = cong (D B) (φ .snd .pres0) ∙ isZarMapD B .pres0
 pres1 isZarMapDcomp = cong (D B) (φ .snd .pres1) ∙ isZarMapD B .pres1
 ·≡∧ isZarMapDcomp f g = cong (D B) (φ .snd .pres· f g)
                    ∙ isZarMapD B .·≡∧ (φ .fst f) (φ .fst g)
 +≤∨ isZarMapDcomp f g =
   let open JoinSemilattice
             (Lattice→JoinSemilattice (DistLattice→Lattice (ZariskiLattice B)))
   in subst (λ x → x ≤ (Dcomp f) ∨l (Dcomp g))
            (sym (cong (D B) (φ .snd .pres+ f g)))
            (isZarMapD B .+≤∨ (φ .fst f) (φ .fst g))

 inducedZarLatHom : DistLatticeHom (ZariskiLattice A) (ZariskiLattice B)
 inducedZarLatHom = ZLHasUniversalProp A (ZariskiLattice B) Dcomp isZarMapDcomp .fst .fst

-- functoriality
module _ (A : CommRing ℓ) where
  open ZarLat
  open ZarLatUniversalProp

  inducedZarLatHomId : inducedZarLatHom (idCommRingHom A)
                     ≡ idDistLatticeHom (ZariskiLattice A)
  inducedZarLatHomId =
    cong fst
      (ZLHasUniversalProp A (ZariskiLattice A) (Dcomp (idCommRingHom A))
                                               (isZarMapDcomp (idCommRingHom A)) .snd
        (idDistLatticeHom (ZariskiLattice A) , refl))

module _ {A B C : CommRing ℓ} (φ : CommRingHom A B) (ψ : CommRingHom B C) where
  open ZarLat
  open ZarLatUniversalProp

  inducedZarLatHomSeq : inducedZarLatHom (ψ ∘cr φ)
                      ≡ inducedZarLatHom ψ ∘dl inducedZarLatHom φ
  inducedZarLatHomSeq =
    cong fst
      (ZLHasUniversalProp A (ZariskiLattice C) (Dcomp (ψ ∘cr φ))
                                               (isZarMapDcomp (ψ ∘cr φ)) .snd
        (inducedZarLatHom ψ ∘dl inducedZarLatHom φ , funExt (λ _ → ∨lRid _)))
    where open DistLatticeStr (ZariskiLattice C .snd)

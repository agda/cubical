{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.Categories.DistLatticeSheaf.Extension where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Nat.Order hiding (_≤_)
open import Cubical.Data.FinData
open import Cubical.Data.FinData.Order

open import Cubical.Relation.Binary.Poset
open import Cubical.HITs.PropositionalTruncation

open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Semilattice
open import Cubical.Algebra.Lattice
open import Cubical.Algebra.DistLattice
open import Cubical.Algebra.DistLattice.Basis
open import Cubical.Algebra.DistLattice.BigOps

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Limits.Pullback
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.Limits
open import Cubical.Categories.Limits.RightKan
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Instances.CommRings
open import Cubical.Categories.Instances.Poset
open import Cubical.Categories.Instances.Semilattice
open import Cubical.Categories.Instances.Lattice
open import Cubical.Categories.Instances.DistLattice


open import Cubical.Categories.DistLatticeSheaf.Diagram
open import Cubical.Categories.DistLatticeSheaf.Base

private
  variable
    ℓ ℓ' ℓ'' : Level


module PreSheafExtension (L : DistLattice ℓ) (C : Category ℓ' ℓ'')
                         (limitC : Limits {ℓ} {ℓ} C) (L' : ℙ (fst L)) where

 open Category
 open Functor
 open Cone
 open LimCone

 private
  DLCat = DistLatticeCategory L
  DLSubCat = ΣPropCat  DLCat L'
  DLPreSheaf = Functor (DLCat ^op) C
  DLSubPreSheaf = Functor (DLSubCat ^op) C

  i : Functor DLSubCat DLCat
  F-ob i = fst
  F-hom i f = f
  F-id i = refl
  F-seq i _ _ = refl

 DLRan : DLSubPreSheaf → DLPreSheaf
 DLRan = Ran limitC (i ^opF)

 module _ (isBasisL' : IsBasis L L') (F : DLSubPreSheaf)
          (isSheafF : SheafOnBasis.isDLBasisSheaf L C L' isBasisL' F) where
  open SheafOnBasis L C L' isBasisL'
  open Order (DistLattice→Lattice L)
  open DistLatticeStr (snd L)
  open Join L
  open JoinSemilattice (Lattice→JoinSemilattice (DistLattice→Lattice L))
  open MeetSemilattice (Lattice→MeetSemilattice (DistLattice→Lattice L))
      using (∧≤RCancel ; ∧≤LCancel ; ≤-∧Pres ; ≤-∧RPres ; ≤-∧LPres)
  open PosetStr (IndPoset .snd) hiding (_≤_)
  open IsBasis ⦃...⦄
  open condCone
  private
   instance
    _ = isBasisL'

   F* = T* limitC (i ^opF) F

  -- the crucial lemmas that will gives us the cones needed to construct the unique
  -- arrow in our pullback square below
  module ConeLemmas {n : ℕ} (α : FinVec (fst L) n) (α∈L' : ∀ i → α i ∈ L') where
    private -- some notation
      ⋁α↓ = _↓Diag limitC (i ^opF) F (⋁ α)

      β : (u : fst L) → FinVec (fst L) n
      β u i = u ∧l α i

      β∈L' : ∀ (u : fst L) → u ∈ L' → ∀ i → β u i ∈ L'
      β∈L' u u∈L' i = ∧lClosed _ _ u∈L' (α∈L' i)

      β≡ : ∀ (u : fst L) → u ≤ ⋁ α → u ≡ ⋁ (β u)
      β≡ u u≤⋁α = sym (≤j→≤m _ _ u≤⋁α) ∙ ⋁Meetrdist _ _

      ⋁β∈L' : ∀ (u : fst L) → u ∈ L' → u ≤ ⋁ α → ⋁ (β u) ∈ L'
      ⋁β∈L' u u∈L' u≤⋁α = subst-∈ L' (β≡ u u≤⋁α) u∈L'

      βCone : (c : ob C) (u : fst L) (u∈L' : u ∈ L')
            → Cone (funcComp F (BDiag (λ i → α i , α∈L' i))) c
            → Cone (funcComp F (BDiag (λ i → β u i , β∈L' u u∈L' i))) c
      coneOut (βCone c u u∈L' cc) (sing i) = coneOut cc (sing i)
        ⋆⟨ C ⟩ F .F-hom (≤m→≤j _ _ (∧≤LCancel _ _))
      coneOut (βCone c u u∈L' cc) (pair i j i<j) = coneOut cc (pair i j i<j)
        ⋆⟨ C ⟩ F .F-hom (≤m→≤j _ _ (≤-∧Pres _ _ _ _ (∧≤LCancel _ _) (∧≤LCancel _ _)))
      coneOutCommutes (βCone c u u∈L' cc) {u = v} idAr =
        cong (λ x → coneOut (βCone c u u∈L' cc) v ⋆⟨ C ⟩ x)
             (F-id (funcComp F (BDiag (λ i → β u i , β∈L' u u∈L' i))))
        ∙ ⋆IdR C _
      coneOutCommutes (βCone c u u∈L' cc) (singPairL {i = i} {j} {i<j}) =
          coneOut cc (sing i) ⋆⟨ C ⟩ F .F-hom (≤m→≤j _ _ (∧≤LCancel _ _))
            ⋆⟨ C ⟩ (funcComp F (BDiag (λ i → β u i , β∈L' u u∈L' i)) .F-hom singPairL)
        ≡⟨ ⋆Assoc C _ _ _ ⟩
          coneOut cc (sing i) ⋆⟨ C ⟩ (F .F-hom (≤m→≤j _ _ (∧≤LCancel _ _))
            ⋆⟨ C ⟩ (funcComp F (BDiag (λ i → β u i , β∈L' u u∈L' i)) .F-hom singPairL))
        ≡⟨ cong (λ x → coneOut cc (sing i) ⋆⟨ C ⟩ x) (sym (F .F-seq _ _)) ⟩
          coneOut cc (sing i) ⋆⟨ C ⟩ F .F-hom
            (≤m→≤j _ _ (∧≤LCancel _ _) ⋆⟨ DLCat ^op ⟩
            (BDiag (λ i → β u i , β∈L' u u∈L' i) .F-hom (singPairL {i = i} {j} {i<j})))
        ≡⟨ cong (λ x → coneOut cc (sing i) ⋆⟨ C ⟩ F .F-hom
                {y = β u i ∧l β u j , ∧lClosed _ _ (β∈L' u u∈L' i) (β∈L' u u∈L' j)} x)
                (is-prop-valued _ _ _ _) ⟩
          coneOut cc (sing i)
            ⋆⟨ C ⟩ F .F-hom ((BDiag (λ i → α i , α∈L' i)) .F-hom  (singPairL {i = i} {j} {i<j})
            ⋆⟨ DLCat ^op ⟩ ≤m→≤j _ _ (≤-∧Pres _ _ _ _ (∧≤LCancel _ _) (∧≤LCancel _ _)))
        ≡⟨ cong (λ x → coneOut cc (sing i) ⋆⟨ C ⟩ x) (F .F-seq _ _) ⟩
          coneOut cc (sing i)
            ⋆⟨ C ⟩ ((funcComp F (BDiag (λ i → α i , α∈L' i)) .F-hom  (singPairL {i = i} {j} {i<j}))
            ⋆⟨ C ⟩ F .F-hom (≤m→≤j _ _ (≤-∧Pres _ _ _ _ (∧≤LCancel _ _) (∧≤LCancel _ _))))
        ≡⟨ sym (⋆Assoc C _ _ _) ⟩
          (coneOut cc (sing i)
            ⋆⟨ C ⟩ (funcComp F (BDiag (λ i → α i , α∈L' i)) .F-hom  (singPairL {i = i} {j} {i<j})))
            ⋆⟨ C ⟩ F .F-hom ((≤m→≤j _ _ (≤-∧Pres _ _ _ _ (∧≤LCancel _ _) (∧≤LCancel _ _))))
        ≡⟨ cong (λ x → x ⋆⟨ C ⟩ F .F-hom
                 {y = β u i ∧l β u j , ∧lClosed _ _ (β∈L' u u∈L' i) (β∈L' u u∈L' j)}
                 (≤m→≤j _ _ (≤-∧Pres _ _ _ _ (∧≤LCancel _ _) (∧≤LCancel _ _))))
                 (coneOutCommutes cc (singPairL {i = i} {j} {i<j})) ⟩
          coneOut (βCone c u u∈L' cc) (pair i j i<j) ∎

      coneOutCommutes (βCone c u u∈L' cc) (singPairR {i = i} {j} {i<j}) =
          coneOut cc (sing j) ⋆⟨ C ⟩ F .F-hom (≤m→≤j _ _ (∧≤LCancel _ _))
            ⋆⟨ C ⟩ (funcComp F (BDiag (λ i → β u i , β∈L' u u∈L' i)) .F-hom singPairR)
        ≡⟨ ⋆Assoc C _ _ _ ⟩
          coneOut cc (sing j) ⋆⟨ C ⟩ (F .F-hom (≤m→≤j _ _ (∧≤LCancel _ _))
            ⋆⟨ C ⟩ (funcComp F (BDiag (λ i → β u i , β∈L' u u∈L' i)) .F-hom singPairR))
        ≡⟨ cong (λ x → coneOut cc (sing j) ⋆⟨ C ⟩ x) (sym (F .F-seq _ _)) ⟩
          coneOut cc (sing j) ⋆⟨ C ⟩ F .F-hom
            (≤m→≤j _ _ (∧≤LCancel _ _) ⋆⟨ DLCat ^op ⟩
            (BDiag (λ i → β u i , β∈L' u u∈L' i) .F-hom (singPairR {i = i} {j} {i<j})))
        ≡⟨ cong (λ x → coneOut cc (sing j) ⋆⟨ C ⟩ F .F-hom
                {y = β u i ∧l β u j , ∧lClosed _ _ (β∈L' u u∈L' i) (β∈L' u u∈L' j)} x)
                (is-prop-valued _ _ _ _) ⟩
          coneOut cc (sing j)
            ⋆⟨ C ⟩ F .F-hom ((BDiag (λ i → α i , α∈L' i)) .F-hom (singPairR {i = i} {j} {i<j})
            ⋆⟨ DLCat ^op ⟩ ≤m→≤j _ _ (≤-∧Pres _ _ _ _ (∧≤LCancel _ _) (∧≤LCancel _ _)))
        ≡⟨ cong (λ x → coneOut cc (sing j) ⋆⟨ C ⟩ x) (F .F-seq _ _) ⟩
          coneOut cc (sing j)
            ⋆⟨ C ⟩ ((funcComp F (BDiag (λ i → α i , α∈L' i)) .F-hom (singPairR {i = i} {j} {i<j}))
            ⋆⟨ C ⟩ F .F-hom (≤m→≤j _ _ (≤-∧Pres _ _ _ _ (∧≤LCancel _ _) (∧≤LCancel _ _))))
        ≡⟨ sym (⋆Assoc C _ _ _) ⟩
          (coneOut cc (sing j)
            ⋆⟨ C ⟩ (funcComp F (BDiag (λ i → α i , α∈L' i)) .F-hom (singPairR {i = i} {j} {i<j})))
            ⋆⟨ C ⟩ F .F-hom ((≤m→≤j _ _ (≤-∧Pres _ _ _ _ (∧≤LCancel _ _) (∧≤LCancel _ _))))
        ≡⟨ cong (λ x → x ⋆⟨ C ⟩ F .F-hom
                 {y = β u i ∧l β u j , ∧lClosed _ _ (β∈L' u u∈L' i) (β∈L' u u∈L' j)}
                 (≤m→≤j _ _ (≤-∧Pres _ _ _ _ (∧≤LCancel _ _) (∧≤LCancel _ _))))
                 (coneOutCommutes cc (singPairR {i = i} {j} {i<j})) ⟩
          coneOut (βCone c u u∈L' cc) (pair i j i<j) ∎


      -- this is the crucial application of our assumption that F is a sheaf on L'
      uniqβConeMor : (c : ob C) (cc : Cone (funcComp F (BDiag (λ i → α i , α∈L' i))) c)
                     (u : fst L) (u∈L' : u ∈ L') (u≤⋁α : u ≤ ⋁ α)
                   → ∃![ f ∈ C [ c , F .F-ob (⋁ (β u) , ⋁β∈L' u u∈L' u≤⋁α) ] ]
                       (isConeMor (βCone c u u∈L' cc)
                       (F-cone F (B⋁Cone (λ i → β u i , β∈L' u u∈L' i) (⋁β∈L' u u∈L' u≤⋁α))) f)
      uniqβConeMor c cc u u∈L' u≤⋁α =
        isSheafF (λ i → β u i , β∈L' u u∈L' i) (⋁β∈L' u u∈L' u≤⋁α) c (βCone c u u∈L' cc)


    -- the lemma giving us the desired cone
    lemma1 : (c : ob C) → Cone (funcComp F (BDiag (λ i → α i , α∈L' i))) c → Cone (F* (⋁ α)) c
    coneOut (lemma1 c cc) ((u , u∈L') , u≤⋁α) =
      subst (λ x → C [ c , F .F-ob x ])
            (Σ≡Prop (λ x → L' x .snd) {u = _ , ⋁β∈L' u u∈L' u≤⋁α} (sym (β≡ u u≤⋁α)))
            (uniqβConeMor c cc u u∈L' u≤⋁α .fst .fst)
    coneOutCommutes (lemma1 c cc) {u = ((u , u∈L') , u≤⋁α)} {v = ((v , v∈L') , v≤⋁α)} (v≤u , p) =
      transport (λ i → fᵤPathP i ⋆⟨ C ⟩ ePathP i ≡ fᵥPathP i) triangle
      where
      e : C [ F .F-ob (⋁ (β u) , ⋁β∈L' u u∈L' u≤⋁α) , F .F-ob (⋁ (β v) , ⋁β∈L' v v∈L' v≤⋁α) ]
      e = F .F-hom (subst2 _≤_ (β≡ v v≤⋁α) (β≡ u u≤⋁α) v≤u) -- F(⋁βᵥ≤⋁βᵤ)

      fᵤ : C [ c , F .F-ob (⋁ (β u) , ⋁β∈L' u u∈L' u≤⋁α) ]
      fᵤ = uniqβConeMor c cc u u∈L' u≤⋁α .fst .fst

      fᵥ : C [ c , F .F-ob (⋁ (β v) , ⋁β∈L' v v∈L' v≤⋁α) ]
      fᵥ = uniqβConeMor c cc v v∈L' v≤⋁α .fst .fst

      -- for convenience
      pᵤ = (Σ≡Prop (λ x → L' x .snd) {u = _ , ⋁β∈L' u u∈L' u≤⋁α} (sym (β≡ u u≤⋁α)))
      pᵥ = (Σ≡Prop (λ x → L' x .snd) {u = _ , ⋁β∈L' v v∈L' v≤⋁α} (sym (β≡ v v≤⋁α)))

      fᵤPathP : PathP (λ i → C [ c , F .F-ob (pᵤ i) ])
                  fᵤ (coneOut (lemma1 c cc) ((u , u∈L') , u≤⋁α))
      fᵤPathP = subst-filler (λ x → C [ c , F .F-ob x ]) pᵤ fᵤ

      fᵥPathP : PathP (λ i → C [ c , F .F-ob (pᵥ i) ])
                  fᵥ (coneOut (lemma1 c cc) ((v , v∈L') , v≤⋁α))
      fᵥPathP = subst-filler (λ x → C [ c , F .F-ob x ]) pᵥ fᵥ

      ePathP : PathP (λ i → C [ F .F-ob (pᵤ i) , F .F-ob (pᵥ i) ]) e (F .F-hom v≤u)
      ePathP i = F .F-hom (subst2-filler (_≤_) (β≡ v v≤⋁α) (β≡ u u≤⋁α) v≤u (~ i))


      -- triangle to be transported by universal property
      triangle : fᵤ ⋆⟨ C ⟩ e ≡ fᵥ
      triangle = sym (cong fst (uniqβConeMor c cc v v∈L' v≤⋁α .snd (fᵤ ⋆⟨ C ⟩ e , compIsConeMor)))
        where
        compIsConeMor : isConeMor (βCone c v v∈L' cc)
                         (F-cone F (B⋁Cone (λ i → β v i , β∈L' v v∈L' i) (⋁β∈L' v v∈L' v≤⋁α)))
                         (fᵤ ⋆⟨ C ⟩ e)
        compIsConeMor (sing i) =
            (fᵤ ⋆⟨ C ⟩ e) ⋆⟨ C ⟩ F .F-hom (ind≤⋁ (β v) i)
          ≡⟨ ⋆Assoc C _ _ _ ⟩
            fᵤ ⋆⟨ C ⟩ (e ⋆⟨ C ⟩ F .F-hom (ind≤⋁ (β v) i))
          ≡⟨ cong (λ x → fᵤ ⋆⟨ C ⟩ x) (sym (F .F-seq _ _))  ⟩
            fᵤ ⋆⟨ C ⟩ F .F-hom
              (subst2 _≤_ (β≡ v v≤⋁α) (β≡ u u≤⋁α) v≤u ⋆⟨ DLCat ^op ⟩ ind≤⋁ (β v) i)
          ≡⟨ cong (λ x → fᵤ ⋆⟨ C ⟩ F .F-hom {y = _ , ∧lClosed _ _ v∈L' (α∈L' i)} x)
                  (is-prop-valued _ _ _ _) ⟩
            fᵤ ⋆⟨ C ⟩ F .F-hom
              (ind≤⋁ (β u) i ⋆⟨ DLCat ^op ⟩ ≤m→≤j _ _ (≤-∧RPres _ _ _ (≤j→≤m _ _ v≤u)))
          ≡⟨ cong (λ x → fᵤ ⋆⟨ C ⟩ x) (F .F-seq _ _) ⟩
            fᵤ ⋆⟨ C ⟩ (F .F-hom {y = _ , ∧lClosed _ _ u∈L' (α∈L' i)} (ind≤⋁ (β u) i)
               ⋆⟨ C ⟩ F .F-hom (≤m→≤j _ _ (≤-∧RPres _ _ _ (≤j→≤m _ _ v≤u))))
          ≡⟨ sym (⋆Assoc C _ _ _) ⟩
            (fᵤ ⋆⟨ C ⟩ F .F-hom {y = _ , ∧lClosed _ _ u∈L' (α∈L' i)} (ind≤⋁ (β u) i))
                ⋆⟨ C ⟩ F .F-hom (≤m→≤j _ _ (≤-∧RPres _ _ _ (≤j→≤m _ _ v≤u)))
          ≡⟨ cong (λ x → x ⋆⟨ C ⟩ F .F-hom (≤m→≤j _ _ (≤-∧RPres _ _ _ (≤j→≤m _ _ v≤u))))
                  (uniqβConeMor c cc u u∈L' u≤⋁α .fst .snd (sing i)) ⟩
            (coneOut cc (sing i) ⋆⟨ C ⟩ F .F-hom {y = _ , ∧lClosed _ _ u∈L' (α∈L' i)}
                                                  (≤m→≤j (u ∧l α i) (α i) (∧≤LCancel _ _)))
                                 ⋆⟨ C ⟩ F .F-hom (≤m→≤j _ _ (≤-∧RPres _ _ _ (≤j→≤m _ _ v≤u)))
          ≡⟨ ⋆Assoc C _ _ _ ⟩
            coneOut cc (sing i) ⋆⟨ C ⟩ (F .F-hom {y = _ , ∧lClosed _ _ u∈L' (α∈L' i)}
                                                  (≤m→≤j (u ∧l α i) (α i) (∧≤LCancel _ _))
                                ⋆⟨ C ⟩ F .F-hom (≤m→≤j _ _ (≤-∧RPres _ _ _ (≤j→≤m _ _ v≤u))))
          ≡⟨ cong (λ x → coneOut cc (sing i) ⋆⟨ C ⟩ x) (sym (F .F-seq _ _)) ⟩
            coneOut cc (sing i) ⋆⟨ C ⟩ F .F-hom
              (≤m→≤j (u ∧l α i) (α i) (∧≤LCancel _ _)
                ⋆⟨ DLCat ^op ⟩ ≤m→≤j _ _ (≤-∧RPres _ _ _ (≤j→≤m _ _ v≤u)))
          ≡⟨ cong (λ x → coneOut cc (sing i) ⋆⟨ C ⟩ F .F-hom {y = _ , ∧lClosed _ _ v∈L' (α∈L' i)} x)
                 (is-prop-valued _ _ _ _) ⟩
            coneOut cc (sing i) ⋆⟨ C ⟩ F .F-hom (≤m→≤j (v ∧l α i) (α i) (∧≤LCancel _ _)) ∎

        compIsConeMor (pair i j i<j) =
            (fᵤ ⋆⟨ C ⟩ e)
                ⋆⟨ C ⟩ F .F-hom (is-trans _ (β v i) _ (≤m→≤j _ _ (∧≤RCancel _ _)) (ind≤⋁ (β v) i))
          ≡⟨ ⋆Assoc C _ _ _ ⟩
            fᵤ ⋆⟨ C ⟩
              (e ⋆⟨ C ⟩ F .F-hom (is-trans _ (β v i) _ (≤m→≤j _ _ (∧≤RCancel _ _)) (ind≤⋁ (β v) i)))
          ≡⟨ cong (λ x → fᵤ ⋆⟨ C ⟩ x) (sym (F .F-seq _ _))  ⟩
            fᵤ ⋆⟨ C ⟩ F .F-hom
              (subst2 _≤_ (β≡ v v≤⋁α) (β≡ u u≤⋁α) v≤u
                ⋆⟨ DLCat ^op ⟩ is-trans _ (β v i) _ (≤m→≤j _ _ (∧≤RCancel _ _)) (ind≤⋁ (β v) i))
          ≡⟨ cong (λ x → fᵤ ⋆⟨ C ⟩ F .F-hom
                  {y = _ , ∧lClosed _ _ (∧lClosed _ _ v∈L' (α∈L' i)) (∧lClosed _ _ v∈L' (α∈L' j))} x)
                  (is-prop-valued _ _ _ _) ⟩
            fᵤ ⋆⟨ C ⟩ F .F-hom (is-trans _ (β u i) _ (≤m→≤j _ _ (∧≤RCancel _ _)) (ind≤⋁ (β u) i)
               ⋆⟨ DLCat ^op ⟩ ≤m→≤j _ _ (≤-∧Pres _ _ _ _ (≤-∧RPres _ _ _ (≤j→≤m _ _ v≤u))
                                        (≤-∧RPres _ _ _ (≤j→≤m _ _ v≤u))))
          ≡⟨ cong (λ x → fᵤ ⋆⟨ C ⟩ x) (F .F-seq _ _) ⟩
            fᵤ ⋆⟨ C ⟩ (F .F-hom (is-trans _ (β u i) _ (≤m→≤j _ _ (∧≤RCancel _ _)) (ind≤⋁ (β u) i))
               ⋆⟨ C ⟩ F .F-hom (≤m→≤j _ _ (≤-∧Pres _ _ _ _ (≤-∧RPres _ _ _ (≤j→≤m _ _ v≤u))
                                                           (≤-∧RPres _ _ _ (≤j→≤m _ _ v≤u)))))
          ≡⟨ sym (⋆Assoc C _ _ _) ⟩
            fᵤ ⋆⟨ C ⟩ F .F-hom (is-trans _ (β u i) _ (≤m→≤j _ _ (∧≤RCancel _ _)) (ind≤⋁ (β u) i))
               ⋆⟨ C ⟩ F .F-hom (≤m→≤j _ _ (≤-∧Pres _ _ _ _ (≤-∧RPres _ _ _ (≤j→≤m _ _ v≤u))
                                                           (≤-∧RPres _ _ _ (≤j→≤m _ _ v≤u))))
          ≡⟨ cong (λ x → x ⋆⟨ C ⟩ F .F-hom
                 (≤m→≤j _ _ (≤-∧Pres _ _ _ _ (≤-∧RPres _ _ _ (≤j→≤m _ _ v≤u))
                                             (≤-∧RPres _ _ _ (≤j→≤m _ _ v≤u)))))
                 (uniqβConeMor c cc u u∈L' u≤⋁α .fst .snd (pair i j i<j)) ⟩
            coneOut (βCone c u u∈L' cc) (pair i j i<j)
               ⋆⟨ C ⟩ F .F-hom (≤m→≤j _ _ (≤-∧Pres _ _ _ _ (≤-∧RPres _ _ _ (≤j→≤m _ _ v≤u))
                                          (≤-∧RPres _ _ _ (≤j→≤m _ _ v≤u))))
          ≡⟨ ⋆Assoc C _ _ _ ⟩
            coneOut cc (pair i j i<j) ⋆⟨ C ⟩ (F .F-hom
                 {y = _ , ∧lClosed _ _ (∧lClosed _ _ u∈L' (α∈L' i)) (∧lClosed _ _ u∈L' (α∈L' j))}
                 (≤m→≤j _ _ (≤-∧Pres _ _ _ _ (∧≤LCancel u _) (∧≤LCancel u _)))
               ⋆⟨ C ⟩ F .F-hom
                 (≤m→≤j _ _ (≤-∧Pres _ _ _ _ (≤-∧RPres _ _ _ (≤j→≤m _ _ v≤u))
                                             (≤-∧RPres _ _ _ (≤j→≤m _ _ v≤u)))))
          ≡⟨ cong (λ x → coneOut cc (pair i j i<j) ⋆⟨ C ⟩ x) (sym (F .F-seq _ _)) ⟩
            coneOut cc (pair i j i<j) ⋆⟨ C ⟩ F .F-hom
                 ((≤m→≤j _ _ (≤-∧Pres _ _ _ _ (∧≤LCancel u _) (∧≤LCancel u _)) ⋆⟨ DLCat ^op ⟩
                 (≤m→≤j _ _ (≤-∧Pres _ _ _ _ (≤-∧RPres _ _ _ (≤j→≤m _ _ v≤u))
                                             (≤-∧RPres _ _ _ (≤j→≤m _ _ v≤u))))))
          ≡⟨ cong (λ x → coneOut cc (pair i j i<j) ⋆⟨ C ⟩ F .F-hom
                  {y = _ , ∧lClosed _ _ (∧lClosed _ _ v∈L' (α∈L' i)) (∧lClosed _ _ v∈L' (α∈L' j))} x)
                  (is-prop-valued _ _ _ _) ⟩
            coneOut cc (pair i j i<j) ⋆⟨ C ⟩
              F .F-hom (≤m→≤j _ _ (≤-∧Pres _ _ _ _ (∧≤LCancel _ _) (∧≤LCancel _ _))) ∎


    -- more notation for second lemma
    -- this is the restriction of the limiting cone through which we define
    -- the Kan-extension to the αᵢ's
    private
      F[⋁α]Cone = limitC ⋁α↓ (F* (⋁ α)) .limCone

    restCone : Cone (funcComp F (BDiag (λ i → α i , α∈L' i))) (DLRan F .F-ob (⋁ α))
    coneOut restCone (sing i) = F[⋁α]Cone .coneOut ((α i , α∈L' i) , ind≤⋁ α i)
    coneOut restCone (pair i j i<j) = F[⋁α]Cone .coneOut
                     ((α i ∧l α j , ∧lClosed _ _ (α∈L' i) (α∈L' j))
                   , is-trans _ (α i) _ (≤m→≤j _ _ (∧≤RCancel _ _)) (ind≤⋁ α i))
    coneOutCommutes restCone {u = sing i} idAr = F[⋁α]Cone .coneOutCommutes
                                                   (is-refl _ , is-prop-valued _ _ _ _)
    coneOutCommutes restCone {u = pair i j i<j} idAr = F[⋁α]Cone .coneOutCommutes
                                                   (is-refl _ , is-prop-valued _ _ _ _)
    coneOutCommutes restCone singPairL = F[⋁α]Cone .coneOutCommutes
                                           (≤m→≤j _ _ (∧≤RCancel _ _) , is-prop-valued _ _ _ _)
    coneOutCommutes restCone singPairR = F[⋁α]Cone .coneOutCommutes
                                           (≤m→≤j _ _ (∧≤LCancel _ _) , is-prop-valued _ _ _ _)

    -- gives us preservation of cone morphisms that ensure uniqueness
    lemma2 : ∀ (c : ob C) (cc : Cone (funcComp F (BDiag (λ i → α i , α∈L' i))) c)
               (f : C [ c , (DLRan F .F-ob (⋁ α)) ])
           → isConeMor cc restCone f
           → isConeMor (lemma1 c cc)  F[⋁α]Cone f
    lemma2 c cc f isRestConeMorf ((u , u∈L') , u≤⋁α) =
      transport (λ i → f ⋆⟨ C ⟩ coneOutPathP i ≡ bᵤPathP i) triangle
      where
      -- for convenience
      pᵤ = Σ≡Prop (λ x → L' x .snd) {u = _ , ⋁β∈L' u u∈L' u≤⋁α}
                                    {v = _ , u∈L'} (sym (β≡ u u≤⋁α))

      bᵤ : C [ c , F .F-ob (⋁ (β u) , ⋁β∈L' u u∈L' u≤⋁α) ]
      bᵤ = uniqβConeMor c cc u u∈L' u≤⋁α .fst .fst

      bᵤPathP : PathP (λ i → C [ c , F .F-ob (pᵤ i) ])
                  bᵤ (coneOut (lemma1 c cc) ((u , u∈L') , u≤⋁α))
      bᵤPathP = subst-filler (λ x → C [ c , F .F-ob x ]) pᵤ bᵤ


      ⋁βᵤ : ob ⋁α↓
      ⋁βᵤ = ((⋁ (β u) , ⋁β∈L' u u∈L' u≤⋁α) , subst (_≤ ⋁ α) (β≡ u u≤⋁α) u≤⋁α)

      coneOutPathP : PathP (λ i → C [ (DLRan F .F-ob (⋁ α)) , F .F-ob (pᵤ i) ])
                       (coneOut F[⋁α]Cone ⋁βᵤ) (coneOut F[⋁α]Cone ((u , u∈L') , u≤⋁α))
      coneOutPathP i = coneOut F[⋁α]Cone ((pᵤ i) , subst-filler (_≤ ⋁ α) (β≡ u u≤⋁α) u≤⋁α (~ i))

      triangle : f ⋆⟨ C ⟩ coneOut F[⋁α]Cone ⋁βᵤ ≡ bᵤ
      triangle = sym (cong fst (uniqβConeMor c cc u u∈L' u≤⋁α .snd
                               (f ⋆⟨ C ⟩ coneOut F[⋁α]Cone ⋁βᵤ , compIsConeMor)))
        where
        compIsConeMor : isConeMor (βCone c u u∈L' cc)
                         (F-cone F (B⋁Cone (λ i → β u i , β∈L' u u∈L' i) (⋁β∈L' u u∈L' u≤⋁α)))
                         (f ⋆⟨ C ⟩ coneOut F[⋁α]Cone ⋁βᵤ)
        compIsConeMor v = {!!}


---- the main proof --------------------------------------------------------------------------------
  isDLSheafDLRan : isDLSheafPullback L C (DLRan F)
  fst isDLSheafDLRan x =
      limArrow (limitC _ (F* 0l)) x (toCone x)
    , λ f → limArrowUnique (limitC _ (F* 0l)) x (toCone x) f (toConeMor x f)
    where
    0↓ = _↓Diag limitC (i ^opF) F 0l

    toTerminal : ∀ (u : ob 0↓) → isTerminal C (F .F-ob (u .fst))
    toTerminal ((u , u∈L') , 0≥u) = subst (λ v → isTerminal C (F .F-ob v))
                                          (Σ≡Prop (λ y → L' y .snd) 0≡u)
                                          (DLBasisSheaf→Terminal F isSheafF 0∈L')
        where
        0≡u : 0l ≡ u
        0≡u = is-antisym _ _ (∨lLid _) 0≥u
        0∈L' : 0l ∈ L'
        0∈L' = subst-∈ L' (sym 0≡u) u∈L'

    toCone : (y : ob C) → Cone (F* 0l) y
    coneOut (toCone y) u = toTerminal u y .fst
    coneOutCommutes (toCone y) {v = v} e = sym (toTerminal v y .snd _)

    toConeMor : (y : ob C) (f : C [ y , F-ob (DLRan F) 0l ])
              → isConeMor (toCone y) (limCone (limitC 0↓ (F* 0l))) f
    toConeMor y f v = sym (toTerminal v y .snd _)


  snd isDLSheafDLRan x y = rec2 (isPropIsPullback _ _ _ _ (Fsq L C x y (DLRan F)))
                             Σhelper (⋁Basis x) (⋁Basis y)
    where
    Σhelper : Σ[ n ∈ ℕ ] Σ[ β ∈ FinVec (fst L) n ] (∀ i → β i ∈ L') × (⋁ β ≡ x)
            → Σ[ m ∈ ℕ ] Σ[ γ ∈ FinVec (fst L) m ] (∀ i → γ i ∈ L') × (⋁ γ ≡ y)
            → isPullback C _ _ _ (Fsq L C x y (DLRan F))
    Σhelper (n , β , β∈L' , ⋁β≡x) (n' , γ , γ∈L' , ⋁γ≡y) =
      transport (λ i → isPullback C (cospanPath i) (pbPr₁PathP i) (pbPr₂PathP i) (squarePathP i))
                (univProp ⋁Pullback)
      where
      open Cospan
      open Pullback
      ⋁β++γ≡x∨y : ⋁ (β ++Fin γ) ≡ x ∨l y
      ⋁β++γ≡x∨y = ⋁Split++ β γ ∙ cong₂ (_∨l_) ⋁β≡x ⋁γ≡y

      β++γ∈L' : ∀ i → (β ++Fin γ) i ∈ L'
      β++γ∈L' i = {!FinSumChar.inv _ _ i!} -- doesn't let you use with-abstraction (C-c C-h)

      -- replace x and y by their representations of joins of base elements
      -- and transport over
      xyCospan : Cospan C
      l xyCospan = DLRan F .F-ob y
      m xyCospan = DLRan F .F-ob (x ∧l y)
      r xyCospan = DLRan F .F-ob x
      s₁ xyCospan = DLRan F .F-hom (≤m→≤j _ _ (∧≤LCancel _ _))
      s₂ xyCospan = DLRan F .F-hom (≤m→≤j _ _ (∧≤RCancel _ _))

      ⋁Cospan : Cospan C
      l ⋁Cospan = DLRan F .F-ob (⋁ γ)
      m ⋁Cospan = DLRan F .F-ob (⋁ β ∧l ⋁ γ)
      r ⋁Cospan = DLRan F .F-ob (⋁ β)
      s₁ ⋁Cospan = DLRan F .F-hom (≤m→≤j _ _ (∧≤LCancel _ _))
      s₂ ⋁Cospan = DLRan F .F-hom (≤m→≤j _ _ (∧≤RCancel _ _))

      cospanPath : ⋁Cospan ≡ xyCospan
      l (cospanPath i) = DLRan F .F-ob (⋁γ≡y i)
      m (cospanPath i) = DLRan F .F-ob (⋁β≡x i ∧l ⋁γ≡y i)
      r (cospanPath i) = DLRan F .F-ob (⋁β≡x i)
      s₁ (cospanPath i) = DLRan F .F-hom (≤m→≤j _ _ (∧≤LCancel _ _))
      s₂ (cospanPath i) = DLRan F .F-hom (≤m→≤j _ _ (∧≤RCancel _ _))

      -- the pullback square we want
      ⋁Pullback : Pullback C ⋁Cospan
      pbOb ⋁Pullback = DLRan F .F-ob (⋁ (β ++Fin γ))
      pbPr₁ ⋁Pullback = DLRan F .F-hom (subst (⋁ γ ≤_) (sym (⋁Split++ β γ)) (∨≤LCancel _ _))
      pbPr₂ ⋁Pullback = DLRan F .F-hom (subst (⋁ β ≤_) (sym (⋁Split++ β γ)) (∨≤RCancel _ _))
      pbCommutes ⋁Pullback = F-square (DLRan F) (is-prop-valued _ _ _ _)
      univProp ⋁Pullback {d = c} f g square = uniqueExists
        (applyLemma1 f g square .fst .fst)
          (fromConeMor _ (applyLemma1 f g square .fst .snd))
            (λ _ → isProp× (isSetHom C _ _) (isSetHom C _ _))
              λ h' trs → cong fst (applyLemma1 f g square .snd -- lemma 2 ensures uniqueness
                (h' , lemma2 _ (toCone f g square) _ (toConeMor f g square h' trs)))
        where -- this is where we apply our lemmas
        open ConeLemmas (β ++Fin γ) β++γ∈L'
        theLimit = limitC _ (F* (⋁ (β ++Fin γ)))
        -- should toCone and toConeMor be upstreamed?
        toCone : (f : C [ c , ⋁Cospan .l ]) (g : C [ c , ⋁Cospan .r ])
               → f ⋆⟨ C ⟩ ⋁Cospan .s₁ ≡ g ⋆⟨ C ⟩ ⋁Cospan .s₂
               → Cone (funcComp F (BDiag (λ i → (β ++Fin γ) i , β++γ∈L' i))) c
        toCone = {!!}

        toConeMor : (f : C [ c , ⋁Cospan .l ]) (g : C [ c , ⋁Cospan .r ])
                    (square : f ⋆⟨ C ⟩ ⋁Cospan .s₁ ≡ g ⋆⟨ C ⟩ ⋁Cospan .s₂)
                    (h : C [ c , ⋁Pullback .pbOb ])
                  → (f ≡ h ⋆⟨ C ⟩ ⋁Pullback .pbPr₁) × (g ≡ h ⋆⟨ C ⟩ ⋁Pullback .pbPr₂)
                  → isConeMor (toCone f g square) restCone h
        toConeMor = {!!}

        applyLemma1 : (f : C [ c , ⋁Cospan .l ]) (g : C [ c , ⋁Cospan .r ])
                      (square : f ⋆⟨ C ⟩ ⋁Cospan .s₁ ≡ g ⋆⟨ C ⟩ ⋁Cospan .s₂)
                    → ∃![ h ∈ C [ c , ⋁Pullback .pbOb ] ]
                        isConeMor (lemma1 c (toCone f g square)) (limCone theLimit) h
        applyLemma1 f g square = univProp theLimit _ _

        fromConeMor : (h : C [ c , ⋁Pullback .pbOb ])
                    → isConeMor (lemma1 c (toCone f g square)) (limCone theLimit) h
                    → (f ≡ h ⋆⟨ C ⟩ ⋁Pullback .pbPr₁) × (g ≡ h ⋆⟨ C ⟩ ⋁Pullback .pbPr₂)
        fromConeMor h hIsConeMor = {!!}


      -- some more names to make the transport readable
      pbPr₁PathP : PathP (λ i → C [ DLRan F .F-ob (⋁β++γ≡x∨y i) , DLRan F .F-ob (⋁γ≡y i) ])
                         (pbPr₁ ⋁Pullback) (DLRan F .F-hom (hom-∨₂ L C x y))
      pbPr₁PathP i = DLRan F .F-hom
                       (isProp→PathP {B = λ i → (⋁γ≡y i) ≤ (⋁β++γ≡x∨y i)}
                                     (λ _ → is-prop-valued _ _)
                                     (subst (⋁ γ ≤_) (sym (⋁Split++ β γ)) (∨≤LCancel _ _))
                                     (hom-∨₂ L C x y) i)

      pbPr₂PathP : PathP (λ i → C [ DLRan F .F-ob (⋁β++γ≡x∨y i) , DLRan F .F-ob (⋁β≡x i) ])
                         (pbPr₂ ⋁Pullback) (DLRan F .F-hom (hom-∨₁ L C x y))
      pbPr₂PathP i = DLRan F .F-hom
                       (isProp→PathP {B = λ i → (⋁β≡x i) ≤ (⋁β++γ≡x∨y i)}
                                     (λ _ → is-prop-valued _ _)
                                     (subst (⋁ β ≤_) (sym (⋁Split++ β γ)) (∨≤RCancel _ _))
                                     (hom-∨₁ L C x y) i)

      squarePathP : PathP (λ i → pbPr₁PathP i ⋆⟨ C ⟩ cospanPath i .s₁
                               ≡ pbPr₂PathP i ⋆⟨ C ⟩ cospanPath i .s₂)
                          (pbCommutes ⋁Pullback) (Fsq L C x y (DLRan F))
      squarePathP = toPathP (isSetHom C _ _ _ _)

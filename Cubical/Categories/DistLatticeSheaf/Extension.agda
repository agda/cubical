{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.Categories.DistLatticeSheaf.Extension where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ ; _+_)
open import Cubical.Data.Nat.Order hiding (_≤_)
open import Cubical.Data.FinData
open import Cubical.Data.FinData.Order
open import Cubical.Data.Sum

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

 open Category hiding (_∘_)
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
  module _ {n : ℕ} (α : FinVec (fst L) n) (α∈L' : ∀ i → α i ∈ L') where
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
        compIsConeMor = isConeMorSingLemma _ (βCone c u u∈L' cc)
                          (F-cone F (B⋁Cone (λ i → β u i , β∈L' u u∈L' i) (⋁β∈L' u u∈L' u≤⋁α)))
                          singCase
          where
          u∧αᵢ≤⋁α : ∀ i → (DLCat ^op) [ ⋁ α , u ∧l α i ]
          u∧αᵢ≤⋁α _ = is-trans _ _ _ (≤m→≤j _ _ (∧≤RCancel _ _)) u≤⋁α

          singCase : ∀ i → (f ⋆⟨ C ⟩ coneOut F[⋁α]Cone ⋁βᵤ) ⋆⟨ C ⟩ F .F-hom (ind≤⋁ (β u) i)
                         ≡ coneOut (βCone c u u∈L' cc) (sing i)
          singCase i =
              (f ⋆⟨ C ⟩ coneOut F[⋁α]Cone ⋁βᵤ) ⋆⟨ C ⟩ F .F-hom (ind≤⋁ (β u) i)
            ≡⟨ ⋆Assoc C _ _ _ ⟩
              f ⋆⟨ C ⟩ (coneOut F[⋁α]Cone ⋁βᵤ ⋆⟨ C ⟩ F .F-hom (ind≤⋁ (β u) i))
            ≡⟨ cong (λ x → f ⋆⟨ C ⟩ x)
                    (coneOutCommutes F[⋁α]Cone (ind≤⋁ (β u) i , is-prop-valued _ _ _ _)) ⟩
              f ⋆⟨ C ⟩ coneOut F[⋁α]Cone ((u ∧l α i , ∧lClosed _ _ u∈L' (α∈L' i)) , u∧αᵢ≤⋁α i)
            ≡⟨ cong (λ x → f ⋆⟨ C ⟩ x) (sym (coneOutCommutes F[⋁α]Cone
                    (≤m→≤j _ _ (∧≤LCancel _ _) , is-prop-valued _ _ _ _))) ⟩
              f ⋆⟨ C ⟩ (coneOut F[⋁α]Cone ((α i , α∈L' i) , ind≤⋁ α i)
                ⋆⟨ C ⟩ F .F-hom (≤m→≤j _ _ (∧≤LCancel _ _)))
            ≡⟨ sym (⋆Assoc C _ _ _) ⟩
              (f ⋆⟨ C ⟩ coneOut F[⋁α]Cone ((α i , α∈L' i) , ind≤⋁ α i))
                 ⋆⟨ C ⟩ F .F-hom (≤m→≤j _ _ (∧≤LCancel _ _))
            ≡⟨ cong (λ x → x ⋆⟨ C ⟩ F .F-hom (≤m→≤j _ _ (∧≤LCancel _ _))) (isRestConeMorf (sing i)) ⟩
              coneOut cc (sing i) ⋆⟨ C ⟩ F .F-hom (≤m→≤j _ _ (∧≤LCancel _ _)) ∎

    -- the other direction, surprisingly hard
    lemma3 : ∀ (c : ob C) (cc : Cone (funcComp F (BDiag (λ i → α i , α∈L' i))) c)
               (f : C [ c , DLRan F .F-ob (⋁ α) ])
           → isConeMor (lemma1 c cc) F[⋁α]Cone f
           → isConeMor cc restCone f
    lemma3 c cc f isConeMorF = isConeMorSingLemma _ cc restCone singCase
      where
      singCase : ∀ i → f ⋆⟨ C ⟩ coneOut restCone (sing i) ≡ coneOut cc (sing i)
      singCase i =
        (subst (λ g → f ⋆⟨ C ⟩ (F[⋁α]Cone .coneOut ((α i , α∈L' i) , ind≤⋁ α i)) ≡ g)
          (transport (λ j → baz j ≡ foo (~ j)) ccᵢSubstPath)
            assumption)
        where
        assumption : f ⋆⟨ C ⟩ (F[⋁α]Cone .coneOut ((α i , α∈L' i) , ind≤⋁ α i))
                   ≡ coneOut (lemma1 c cc) ((α i , α∈L' i) , ind≤⋁ α i)
        assumption = isConeMorF ((α i , α∈L' i) , ind≤⋁ α i)

        -- modulo transport
        Σpathhelper : (α i , α∈L' i) ≡ (⋁ (β (α i)) , ⋁β∈L' (α i) (α∈L' i) (ind≤⋁ α i))
        Σpathhelper = Σ≡Prop (λ x → L' x .snd) (β≡ (α i) (ind≤⋁ α i))

        Σpathhelper2 : (⋁ (β (α i)) , ⋁β∈L' (α i) (α∈L' i) (ind≤⋁ α i)) ≡ (α i , α∈L' i)
        Σpathhelper2 = Σ≡Prop (λ x → L' x .snd) (sym (β≡ (α i) (ind≤⋁ α i)))

        ccᵢSubst : C [ c , F .F-ob  (⋁ (β (α i)) , ⋁β∈L' (α i) (α∈L' i) (ind≤⋁ α i)) ]
        ccᵢSubst = subst (λ x → C [ c , F .F-ob x ])
                     (Σ≡Prop (λ x → L' x .snd) (β≡ (α i) (ind≤⋁ α i)))
                     (coneOut cc (sing i))

        foo : PathP (λ j → C [ c , F .F-ob (Σpathhelper j) ]) (coneOut cc (sing i)) ccᵢSubst
        foo = subst-filler (λ x → C [ c , F .F-ob x ]) Σpathhelper (coneOut cc (sing i))

        bar : PathP (λ j → C [ c , F .F-ob (Σpathhelper2 j) ])
                    (uniqβConeMor c cc (α i) (α∈L' i) (ind≤⋁ α i) .fst .fst)
                    (coneOut (lemma1 c cc) ((α i , α∈L' i) , ind≤⋁ α i))
        bar = subst-filler (λ x → C [ c , F .F-ob x ]) Σpathhelper2 (uniqβConeMor c cc (α i) (α∈L' i) (ind≤⋁ α i) .fst .fst)

        Σpathhelperpath : Σpathhelper2 ≡ sym Σpathhelper
        Σpathhelperpath = isSetL' _ _ _ _
         where
         isSetL' : isSet (ob DLSubCat)
         isSetL' = isSetΣSndProp (isSetDistLattice L) λ x → L' x .snd

        baz : PathP (λ j → C [ c , F .F-ob (Σpathhelper (~ j)) ])
                    (uniqβConeMor c cc (α i) (α∈L' i) (ind≤⋁ α i) .fst .fst)
                    (coneOut (lemma1 c cc) ((α i , α∈L' i) , ind≤⋁ α i))
        baz = subst (λ p → PathP (λ j → C [ c , F .F-ob (p j) ])
                    (uniqβConeMor c cc (α i) (α∈L' i) (ind≤⋁ α i) .fst .fst)
                    (coneOut (lemma1 c cc) ((α i , α∈L' i) , ind≤⋁ α i)))
                    Σpathhelperpath bar

        ccᵢSubstIsConeMor : isConeMor (βCone c (α i) (α∈L' i) cc)
                         (F-cone F (B⋁Cone (λ j → (β (α i) j) , β∈L' (α i) (α∈L' i) j)
                                            (⋁β∈L' (α i) (α∈L' i) (ind≤⋁ α i))))
                         ccᵢSubst
        ccᵢSubstIsConeMor = isConeMorSingLemma _ (βCone c (α i) (α∈L' i) cc)
                         (F-cone F (B⋁Cone (λ j → (β (α i) j) , β∈L' (α i) (α∈L' i) j)
                                            (⋁β∈L' (α i) (α∈L' i) (ind≤⋁ α i))))
                         singCase2
          where
          singCase2 : (j : Fin n) → ccᵢSubst ⋆⟨ C ⟩ F-hom F (ind≤⋁ (β (α i)) j)
                                  ≡ coneOut cc (sing j) ⋆⟨ C ⟩ F .F-hom (≤m→≤j _ _ (∧≤LCancel _ _))
          singCase2 j = (λ 𝕚 → foo (~ 𝕚) ⋆⟨ C ⟩ F .F-hom
                          (isProp→PathP {B = B} (λ _ → is-prop-valued _ _)
                            (ind≤⋁ (β (α i)) j) (≤m→≤j _ _ (∧≤RCancel _ _)) 𝕚))
                      ∙ path
            where
            B : I → Type ℓ
            B = λ 𝕚 → (DLSubCat ^op) [ (Σpathhelper (~ 𝕚)) , (α i ∧l α j , β∈L' (α i) (α∈L' i) j) ]

            path : coneOut cc (sing i) ⋆⟨ C ⟩ F .F-hom (≤m→≤j _ _ (∧≤RCancel _ _))
                 ≡ coneOut cc (sing j) ⋆⟨ C ⟩ F .F-hom (≤m→≤j _ _ (∧≤LCancel _ _))
            path with (i ≟Fin j)
            ... | (lt i<j) = coneOutCommutes cc (singPairL {i<j = i<j})
                           ∙ sym (coneOutCommutes cc singPairR)
            ... | (gt j<i) = transp B2 i0 almostPath
              where
              ∧Path : Path (ob DLSubCat) (α j ∧l α i , β∈L' (α j) (α∈L' j) i)
                                         (α i ∧l α j , β∈L' (α i) (α∈L' i) j)
              ∧Path = Σ≡Prop (λ x → L' x .snd) (∧lComm _ _)

              almostPath : coneOut cc (sing i) ⋆⟨ C ⟩ F .F-hom (≤m→≤j _ _ (∧≤LCancel _ _))
                         ≡ coneOut cc (sing j) ⋆⟨ C ⟩ F .F-hom (≤m→≤j _ _ (∧≤RCancel _ _))
              almostPath = (coneOutCommutes cc (singPairR {i<j = j<i})
                         ∙ sym (coneOutCommutes cc singPairL))

              iPathP : PathP (λ 𝕚 → (DLSubCat ^op) [ (α i , α∈L' i) , ∧Path 𝕚 ])
                             (≤m→≤j _ _ (∧≤LCancel _ _)) (≤m→≤j _ _ (∧≤RCancel _ _))
              iPathP = toPathP (is-prop-valued _ _ _ _)

              jPathP : PathP (λ 𝕚 → (DLSubCat ^op) [ (α j , α∈L' j) , ∧Path 𝕚 ])
                             (≤m→≤j _ _ (∧≤RCancel _ _)) (≤m→≤j _ _ (∧≤LCancel _ _))
              jPathP = toPathP (is-prop-valued _ _ _ _)

              B2 : I → Type ℓ''
              B2 = λ 𝕚 → coneOut cc (sing i) ⋆⟨ C ⟩ F .F-hom {y = ∧Path 𝕚} (iPathP 𝕚)
                       ≡ coneOut cc (sing j) ⋆⟨ C ⟩ F .F-hom (jPathP 𝕚)

            ... | (eq i≡j) =
                coneOut cc (sing i) ⋆⟨ C ⟩ F .F-hom (≤m→≤j _ _ (∧≤RCancel _ _))
              ≡⟨ (λ 𝕚 → coneOut cc (sing (i≡j 𝕚)) ⋆⟨ C ⟩ F .F-hom (isProp→PathP {B = B2}
                           (λ _ → is-prop-valued _ _)
                           (≤m→≤j _ _ (∧≤RCancel _ _)) (≤m→≤j _ _ (∧≤LCancel _ _)) 𝕚)) ⟩
                coneOut cc (sing j) ⋆⟨ C ⟩ F .F-hom (≤m→≤j _ _ (∧≤LCancel _ _)) ∎
                where
                B2 : I → Type ℓ
                B2 = λ 𝕚 → (DLSubCat ^op) [ (α (i≡j 𝕚) , α∈L' (i≡j 𝕚)) , (α i ∧l α j , β∈L' (α i) (α∈L' i) j) ]


        ccᵢSubstPath : uniqβConeMor c cc (α i) (α∈L' i) (ind≤⋁ α i) .fst .fst ≡ ccᵢSubst
        ccᵢSubstPath = cong fst
                     (uniqβConeMor c cc (α i) (α∈L' i) (ind≤⋁ α i) .snd (ccᵢSubst , ccᵢSubstIsConeMor))



    -- putting it all together
    lemma4 : ∀ (c : ob C) (cc : Cone (funcComp F (BDiag (λ i → α i , α∈L' i))) c)
           → ∃![ f ∈ C [ c , DLRan F .F-ob (⋁ α) ] ] isConeMor cc restCone f
    lemma4 c cc = uniqueExists
      (fromUnivProp .fst .fst)
        (lemma3 c cc _ (fromUnivProp .fst .snd))
          (λ _ → isPropIsConeMor _ _ _)
            λ g isConeMorG → cong fst (fromUnivProp .snd (g , lemma2 c cc g isConeMorG))
      where
      fromUnivProp : ∃![ f ∈ C [ c , DLRan F .F-ob (⋁ α) ] ] isConeMor (lemma1 c cc) F[⋁α]Cone f
      fromUnivProp = limitC ⋁α↓ (F* (⋁ α)) .univProp c (lemma1 c cc)


  module ++Lemmas {c : ob C} {n' : ℕ} {γ : FinVec (fst L) n'} {γ∈L' : ∀ i → γ i ∈ L'}
                  (ccγ : Cone (funcComp F (BDiag (λ i → γ i , γ∈L' i))) c) where

    private
      β++γ∈L' : {n : ℕ} {β : FinVec (fst L) n} (β∈L' : ∀ i → β i ∈ L') → ∀ i → (β ++Fin γ) i ∈ L'
      β++γ∈L' β∈L' = ++FinPres∈ L' β∈L' γ∈L'

      β∧γ : {n : ℕ} {β : FinVec (fst L) n} (β∈L' : ∀ i → β i ∈ L')
          → Fin n → Fin n' → ob DLSubCat
      β∧γ {β = β} β∈L' i j = (β i ∧l γ j) , ∧lClosed _ _ (β∈L' i) (γ∈L' j)

      β≥β∧γ : {n : ℕ} {β : FinVec (fst L) n} (β∈L' : ∀ i → β i ∈ L')
            → ∀ i j → (DLSubCat ^op) [ (β i , β∈L' i) , β∧γ β∈L' i j ]
      β≥β∧γ β∈L' i j = ≤m→≤j _ _ (∧≤RCancel _ _)

      γ≥β∧γ : {n : ℕ} {β : FinVec (fst L) n} (β∈L' : ∀ i → β i ∈ L')
            → ∀ i j → (DLSubCat ^op) [ (γ j , γ∈L' j) , β∧γ β∈L' i j ]
      γ≥β∧γ β∈L' i j = ≤m→≤j _ _ (∧≤LCancel _ _)

      CommHypType : {n : ℕ} {β : FinVec (fst L) n} (β∈L' : ∀ i → β i ∈ L')
                    (ccβ : Cone (funcComp F (BDiag (λ i → β i , β∈L' i))) c)
                  → Type ℓ''
      CommHypType β∈L' ccβ = ∀ i j → ccβ .coneOut (sing i)
                                        ⋆⟨ C ⟩ F .F-hom {y = _ , ∧lClosed _ _ (β∈L' i) (γ∈L' j)} (β≥β∧γ β∈L' i j)
                                   ≡ ccγ .coneOut (sing j) ⋆⟨ C ⟩ F .F-hom (γ≥β∧γ β∈L' i j)

      coneSuc : {n : ℕ} {β : FinVec (fst L) (ℕ.suc n)} {β∈L' : ∀ i → β i ∈ L'}
              → Cone (funcComp F (BDiag (λ i → β i , β∈L' i))) c
              → Cone (funcComp F (BDiag (λ i → β (suc i) , β∈L' (suc i)))) c
      coneOut (coneSuc ccβ) (sing i) = coneOut ccβ (sing (suc i))
      coneOut (coneSuc ccβ) (pair i j i<j) = coneOut ccβ (pair (suc i) (suc j) (s≤s i<j))
      coneOutCommutes (coneSuc ccβ) {u = sing i} idAr = coneOutCommutes ccβ idAr
      coneOutCommutes (coneSuc ccβ) {u = pair i j i<j} idAr = coneOutCommutes ccβ idAr
      coneOutCommutes (coneSuc ccβ) singPairL = coneOutCommutes ccβ singPairL
      coneOutCommutes (coneSuc ccβ) singPairR = coneOutCommutes ccβ singPairR

      --make this explicit to avoid yellow
      commHypSuc : {n : ℕ} {β : FinVec (fst L) (ℕ.suc n)} {β∈L' : ∀ i → β i ∈ L'}
                   {ccβ : Cone (funcComp F (BDiag (λ i → β i , β∈L' i))) c}
                 → CommHypType β∈L' ccβ
                 → CommHypType (β∈L' ∘ suc) (coneSuc ccβ)
      commHypSuc commHyp i j = commHyp (suc i) j

      toConeOut : (n : ℕ) (β : FinVec (fst L) n) (β∈L' : ∀ i → β i ∈ L')
                  (ccβ : Cone (funcComp F (BDiag (λ i → β i , β∈L' i))) c)
                  (ch : CommHypType β∈L' ccβ)
               → ∀ (v : DLShfDiagOb (n + n'))
               → C [ c , funcComp F (BDiag (λ i → (β ++Fin γ) i , β++γ∈L' β∈L' i)) .F-ob v ]
      toConeOut ℕ.zero β β∈L' ccβ ch (sing i) = ccγ .coneOut (sing i)
      toConeOut ℕ.zero β β∈L' ccβ ch (pair i j i<j) = ccγ .coneOut (pair i j i<j)
      toConeOut (ℕ.suc n) β β∈L' ccβ ch (sing zero) = ccβ .coneOut (sing zero)
      toConeOut (ℕ.suc n) β β∈L' ccβ ch (sing (suc i)) =
                  toConeOut n (β ∘ suc) (β∈L' ∘ suc) (coneSuc ccβ) (commHypSuc ch) (sing i)
      toConeOut (ℕ.suc n) β β∈L' ccβ ch (pair zero j 0<j) =
                  ccβ .coneOut (sing zero) ⋆⟨ C ⟩ F .F-hom (≤m→≤j _ _ (∧≤RCancel _ _))
      toConeOut (ℕ.suc n) β β∈L' ccβ ch (pair (suc i) zero ())
      toConeOut (ℕ.suc n) β β∈L' ccβ ch (pair (suc i) (suc j) (s≤s i<j)) =
                  toConeOut n (β ∘ suc) (β∈L' ∘ suc) (coneSuc ccβ) (commHypSuc ch) (pair i j i<j)

      -- crucial step in proving that this defines a cone is another induction
      -- βₛ is supposed to be (β ∘ suc) and β₀ is (β zero)
      toConeOutLemma :  (n : ℕ) (βₛ : FinVec (fst L) n) (βₛ∈L' : ∀ i → βₛ i ∈ L')
                        (ccβₛ : Cone (funcComp F (BDiag (λ i → βₛ i , βₛ∈L' i))) c)
                        (chₛ : CommHypType βₛ∈L' ccβₛ)
                        (β₀ : fst L) (β₀∈L' : β₀ ∈ L')
                        -- cone over [β₀]++βₛ
                        {ccβ₀ : C [ c , F .F-ob (β₀ , β₀∈L') ]}
                        {ccβ₀ᵢ : (i : Fin n) → C [ c , F .F-ob (β₀ ∧l βₛ i , ∧lClosed _ _ β₀∈L' (βₛ∈L' i)) ]}
                        (ccβ₀L : ∀ i → ccβ₀ ⋆⟨ C ⟩ F .F-hom (≤m→≤j _ _ (∧≤RCancel _ _)) ≡ ccβ₀ᵢ i)
                        (ccβ₀R : ∀ i → ccβₛ .coneOut (sing i) ⋆⟨ C ⟩ F .F-hom (≤m→≤j _ _ (∧≤LCancel _ _)) ≡ ccβ₀ᵢ i)
                        -- ch at zero
                        (ch₀ : ∀ j → ccβ₀ ⋆⟨ C ⟩ F .F-hom {y = _ , ∧lClosed _ _ β₀∈L' (γ∈L' j)} (≤m→≤j _ _ (∧≤RCancel _ _))
                                   ≡ ccγ .coneOut (sing j) ⋆⟨ C ⟩ F .F-hom (≤m→≤j _ _ (∧≤LCancel _ _)))
                     ----------------------------------------------------------------------------------------------------------
                     → ∀ j → toConeOut n βₛ βₛ∈L' ccβₛ chₛ (sing j)
                                   ⋆⟨ C ⟩ F .F-hom {y = _ ,  ∧lClosed _ _ β₀∈L' (β++γ∈L' βₛ∈L' j)} (≤m→≤j _ _ (∧≤LCancel _ _))
                            ≡ ccβ₀ ⋆⟨ C ⟩ F .F-hom (≤m→≤j _ _ (∧≤RCancel _ _))
      toConeOutLemma ℕ.zero _ _ _ _ _ _ _ _ ch₀ j = sym (ch₀ j)
      toConeOutLemma (ℕ.suc n) _ _ _ _ _ _ ccβ₀L ccβ₀R _ zero = ccβ₀R zero ∙ sym (ccβ₀L zero)
      toConeOutLemma (ℕ.suc n) βₛ βₛ∈L' ccβₛ chₛ β₀ β₀∈L' ccβ₀L ccβ₀R ch₀ (suc j) =
          toConeOutLemma n (βₛ ∘ suc) (βₛ∈L' ∘ suc) (coneSuc ccβₛ) (commHypSuc chₛ) β₀ β₀∈L' (ccβ₀L ∘ suc) (ccβ₀R ∘ suc) ch₀ j


      toConeOutCommutes : (n : ℕ) (β : FinVec (fst L) n) (β∈L' : ∀ i → β i ∈ L')
                          (ccβ : Cone (funcComp F (BDiag (λ i → β i , β∈L' i))) c)
                          (ch : CommHypType β∈L' ccβ)
                        → ∀ {u} {v} e
                        → toConeOut _ _ _ ccβ ch u
                             ⋆⟨ C ⟩ (funcComp F (BDiag (λ i → (β ++Fin γ) i , β++γ∈L' β∈L' i)) .F-hom e)
                        ≡ toConeOut _ _ _ ccβ ch v
      toConeOutCommutes ℕ.zero _ _ _ _ {u = sing i} {v = sing .i} idAr = coneOutCommutes ccγ idAr
      toConeOutCommutes ℕ.zero _ _ _ _ {u = sing i} {v = pair .i j i<j} singPairL = coneOutCommutes ccγ singPairL
      toConeOutCommutes ℕ.zero _ _ _ _ {u = sing j} {v = pair i .j i<j} singPairR = coneOutCommutes ccγ singPairR
      toConeOutCommutes ℕ.zero _ _ _ _ {u = pair i j i<j} {v = sing k} ()
      toConeOutCommutes ℕ.zero _ _ _ _ {u = pair i j i<j} {v = pair .i .j .i<j} idAr = coneOutCommutes ccγ idAr
      toConeOutCommutes (ℕ.suc n) β β∈L' ccβ ch idAr =
          cong (λ x → toConeOut _ _ _ ccβ ch _ ⋆⟨ C ⟩ x) (F .F-id) ∙ ⋆IdR C _
      toConeOutCommutes (ℕ.suc n) β β∈L' ccβ ch (singPairL {i = zero} {j = j} {i<j = i<j}) = refl
      toConeOutCommutes (ℕ.suc n) β β∈L' ccβ ch (singPairL {i = suc i} {j = zero} {i<j = ()})
      toConeOutCommutes (ℕ.suc n) β β∈L' ccβ ch (singPairL {i = suc i} {j = suc j} {i<j = s≤s i<j}) =
          toConeOutCommutes n (β ∘ suc) (β∈L' ∘ suc) (coneSuc ccβ) (commHypSuc ch) singPairL
      toConeOutCommutes (ℕ.suc n) β β∈L' ccβ ch (singPairR {i = suc i} {j = suc j} {i<j = s≤s i<j}) =
          toConeOutCommutes n (β ∘ suc) (β∈L' ∘ suc) (coneSuc ccβ) (commHypSuc ch) singPairR
      toConeOutCommutes (ℕ.suc n) β β∈L' ccβ ch (singPairR {i = zero} {j = suc j} {i<j = s≤s z≤}) =
          toConeOutLemma n (β ∘ suc) (β∈L' ∘ suc) (coneSuc ccβ) (commHypSuc ch) (β zero) (β∈L' zero)
            (λ j → coneOutCommutes ccβ (singPairL {i = zero} {j = suc j} {i<j = s≤s z≤}))
              (λ j → coneOutCommutes ccβ (singPairR {i = zero} {j = suc j} {i<j = s≤s z≤}))
                (ch zero) j

    toCone : {n : ℕ} {β : FinVec (fst L) n} {β∈L' : ∀ i → β i ∈ L'}
             (ccβ : Cone (funcComp F (BDiag (λ i → β i , β∈L' i))) c)
             (ch : CommHypType β∈L' ccβ)
           → Cone (funcComp F (BDiag (λ i → (β ++Fin γ) i , β++γ∈L' β∈L' i))) c
    coneOut (toCone ccβ ch) = toConeOut _ _ _ ccβ ch
    coneOutCommutes (toCone ccβ ch) = toConeOutCommutes _ _ _ ccβ ch




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
      β++γ∈L' = ++FinPres∈ L' β∈L' γ∈L'

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
        (applyLemma4 f g square .fst .fst)
          (fromConeMor _ (applyLemma4 f g square .fst .snd))
            (λ _ → isProp× (isSetHom C _ _) (isSetHom C _ _))
              λ h' trs → cong fst (applyLemma4 f g square .snd (h' , toConeMor f g square h' trs))
        where -- this is where we apply our lemmas
        theLimit = limitC _ (F* (⋁ (β ++Fin γ)))

        -- open FinSumChar renaming (fun to FSCfun ; inv to FSCinv ; sec to FSCsec)
        toCone : (f : C [ c , ⋁Cospan .l ]) (g : C [ c , ⋁Cospan .r ])
               → f ⋆⟨ C ⟩ ⋁Cospan .s₁ ≡ g ⋆⟨ C ⟩ ⋁Cospan .s₂
               → Cone (funcComp F (BDiag (λ i → (β ++Fin γ) i , β++γ∈L' i))) c
        toCone f g square = ++Lemmas.toCone (f ★ (restCone γ γ∈L')) (g ★ (restCone β β∈L')) indSquare
          where
          F[⋁β]Cone = limitC _ (F* (⋁ β)) .limCone
          F[⋁γ]Cone = limitC _ (F* (⋁ γ)) .limCone
          F[⋁β∧⋁γ]Cone = limitC _ (F* (⋁ β ∧l ⋁ γ)) .limCone

          indSquare  : ∀ i j →
              (g ⋆⟨ C ⟩ restCone β β∈L' .coneOut (sing i))
                 ⋆⟨ C ⟩ F .F-hom {y = _ , ∧lClosed _ _ (β∈L' i) (γ∈L' j)} (≤m→≤j _ _ (∧≤RCancel _ _))
            ≡ (f ⋆⟨ C ⟩ restCone γ γ∈L' .coneOut (sing j))
                 ⋆⟨ C ⟩ F .F-hom (≤m→≤j _ _ (∧≤LCancel _ _))
          indSquare i j =
              (g ⋆⟨ C ⟩ restCone β β∈L' .coneOut (sing i))
                 ⋆⟨ C ⟩ F .F-hom (≤m→≤j _ _ (∧≤RCancel _ _))
            ≡⟨ ⋆Assoc C _ _ _ ⟩
              g ⋆⟨ C ⟩ (restCone β β∈L' .coneOut (sing i)
                ⋆⟨ C ⟩ F .F-hom (≤m→≤j _ _ (∧≤RCancel _ _)))
            ≡⟨ cong (λ x → g ⋆⟨ C ⟩ x) (coneOutCommutes F[⋁β]Cone (_ , (is-prop-valued _ _ _ _))) ⟩
              g ⋆⟨ C ⟩ coneOut F[⋁β]Cone ((β i ∧l γ j , _)
                                , is-trans _ _ _ (≤m→≤j _ _ (∧≤RCancel _ _)) (ind≤⋁ β i))
            ≡⟨ cong (λ x → g ⋆⟨ C ⟩ x) (sym (limArrowCommutes {!limitC _ (F* (⋁ β ∧l ⋁ γ))!} {!!} {!!} {!!})) ⟩
              g ⋆⟨ C ⟩ (s₂ ⋁Cospan ⋆⟨ C ⟩ coneOut F[⋁β∧⋁γ]Cone ((β i ∧l γ j , _)
                , (≤m→≤j _ _ (≤-∧Pres _ _ _ _ (≤j→≤m _ _ (ind≤⋁ β i)) (≤j→≤m _ _ (ind≤⋁ γ j))))))
            ≡⟨ sym (⋆Assoc C _ _ _) ⟩
              (g ⋆⟨ C ⟩ s₂ ⋁Cospan) ⋆⟨ C ⟩ coneOut F[⋁β∧⋁γ]Cone ((β i ∧l γ j , _)
                , (≤m→≤j _ _ (≤-∧Pres _ _ _ _ (≤j→≤m _ _ (ind≤⋁ β i)) (≤j→≤m _ _ (ind≤⋁ γ j)))))
            ≡⟨ cong (λ x → x ⋆⟨ C ⟩ coneOut F[⋁β∧⋁γ]Cone ((β i ∧l γ j , ∧lClosed _ _ (β∈L' i) (γ∈L' j))
                  , (≤m→≤j _ _ (≤-∧Pres _ _ _ _ (≤j→≤m _ _ (ind≤⋁ β i)) (≤j→≤m _ _ (ind≤⋁ γ j))))))
                    (sym square) ⟩
              (f ⋆⟨ C ⟩ s₁ ⋁Cospan) ⋆⟨ C ⟩ coneOut F[⋁β∧⋁γ]Cone ((β i ∧l γ j , _)
                , (≤m→≤j _ _ (≤-∧Pres _ _ _ _ (≤j→≤m _ _ (ind≤⋁ β i)) (≤j→≤m _ _ (ind≤⋁ γ j)))))
            ≡⟨ ⋆Assoc C _ _ _ ⟩
              f ⋆⟨ C ⟩ (s₁ ⋁Cospan ⋆⟨ C ⟩ coneOut F[⋁β∧⋁γ]Cone ((β i ∧l γ j , _)
                , (≤m→≤j _ _ (≤-∧Pres _ _ _ _ (≤j→≤m _ _ (ind≤⋁ β i)) (≤j→≤m _ _ (ind≤⋁ γ j))))))
            ≡⟨ {!!} ⟩
              f ⋆⟨ C ⟩ coneOut F[⋁γ]Cone ((β i ∧l γ j , _)
                                , is-trans _ _ _ (≤m→≤j _ _ (∧≤LCancel _ _)) (ind≤⋁ γ j))
            ≡⟨ cong (λ x → f ⋆⟨ C ⟩ x) (sym (coneOutCommutes F[⋁γ]Cone (_ , (is-prop-valued _ _ _ _)))) ⟩
              f ⋆⟨ C ⟩ (restCone γ γ∈L' .coneOut (sing j)
                ⋆⟨ C ⟩ F .F-hom (≤m→≤j _ _ (∧≤LCancel _ _)))
            ≡⟨ sym (⋆Assoc C _ _ _) ⟩
              (f ⋆⟨ C ⟩ restCone γ γ∈L' .coneOut (sing j))
                 ⋆⟨ C ⟩ F .F-hom (≤m→≤j _ _ (∧≤LCancel _ _)) ∎


        -- coneOut (toCone f g square) (sing i) = -- wouldn't work with with-syntax
        --   subst (λ x → C [ c , F-ob F ((β ++Fin γ) x , ++FinPres∈ L' β∈L' γ∈L' x) ])
        --         (FSCsec n n' i)
        --         (coneOutSingAux (FSCinv n n' i))
        --   where
        --   coneOutSingAux : (x : Fin n ⊎ Fin n')
        --                  → C [ c , F-ob F ((β ++Fin γ) (FSCfun _ _ x)
        --                          , ++FinPres∈ L' β∈L' γ∈L' (FSCfun _ _ x)) ]
        --   coneOutSingAux (inl i') = subst (λ x → C [ c , F .F-ob x ])
        --                                   (Σ≡Prop (λ x → L' x .snd) (++FinInl _ _ β γ i'))
        --                                   (g ⋆⟨ C ⟩ coneOut (restCone β β∈L') (sing i'))
        --   coneOutSingAux (inr i') = subst (λ x → C [ c , F .F-ob x ])
        --                                   (Σ≡Prop (λ x → L' x .snd) (++FinInr _ _ β γ i'))
        --                                   (f ⋆⟨ C ⟩ coneOut (restCone γ γ∈L') (sing i'))
        -- coneOut (toCone f g square) (pair i j i<j) = {!!}
        --   where
        --   coneOutPairAux : (x y : Fin n ⊎ Fin n')
        --                  → (FSCfun _ _ x) <'Fin (FSCfun _ _ y)
        --                  → C [ c , F-ob F
        --                      ((β ++Fin γ) (FSCfun _ _ x) ∧l (β ++Fin γ) (FSCfun _ _ y)
        --                      , ∧lClosed ((β ++Fin γ) (FSCfun _ _ x)) ((β ++Fin γ) (FSCfun _ _ y))
        --                          (++FinPres∈ L' β∈L' γ∈L' (FSCfun _ _ x))
        --                          (++FinPres∈ L' β∈L' γ∈L' (FSCfun _ _ y))) ]
        --   coneOutPairAux (inl i') (inl j') i'<j' = {!!}
        --   coneOutPairAux (inl i') (inr j') i'<j' = {!!}
        --   coneOutPairAux (inr i') (inl j') i'<j' = {!!}
        --   coneOutPairAux (inr i') (inr j') i'<j' = {!!}

        -- coneOutCommutes (toCone f g square) = {!!}

        applyLemma4 : (f : C [ c , ⋁Cospan .l ]) (g : C [ c , ⋁Cospan .r ])
                      (square : f ⋆⟨ C ⟩ ⋁Cospan .s₁ ≡ g ⋆⟨ C ⟩ ⋁Cospan .s₂)
                    → ∃![ h ∈ C [ c , ⋁Pullback .pbOb ] ]
                        isConeMor (toCone f g square) (restCone (β ++Fin γ) β++γ∈L') h
        applyLemma4 f g square = lemma4 (β ++Fin γ) β++γ∈L' c (toCone f g square)

        toConeMor : (f : C [ c , ⋁Cospan .l ]) (g : C [ c , ⋁Cospan .r ])
                    (square : f ⋆⟨ C ⟩ ⋁Cospan .s₁ ≡ g ⋆⟨ C ⟩ ⋁Cospan .s₂)
                    (h : C [ c , ⋁Pullback .pbOb ])
                  → (f ≡ h ⋆⟨ C ⟩ ⋁Pullback .pbPr₁) × (g ≡ h ⋆⟨ C ⟩ ⋁Pullback .pbPr₂)
                  → isConeMor (toCone f g square) (restCone (β ++Fin γ) β++γ∈L') h
        toConeMor = {!!}

        fromConeMor : (h : C [ c , ⋁Pullback .pbOb ])
                    → isConeMor (toCone f g square) (restCone (β ++Fin γ) β++γ∈L') h
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

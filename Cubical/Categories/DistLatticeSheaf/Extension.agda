{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.Categories.DistLatticeSheaf.Extension where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Nat.Order
open import Cubical.Data.FinData
open import Cubical.Data.FinData.Order

open import Cubical.Relation.Binary.Poset

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
      using (∧≤RCancel ; ∧≤LCancel ; ≤-∧Pres)
  open PosetStr (IndPoset .snd) hiding (_≤_)
  open IsBasis ⦃...⦄
  open condCone
  private
   instance
    _ = isBasisL'
   F* = T* limitC (i ^opF) F

  coneLemma : ∀ (c : ob C) {n : ℕ} (α : FinVec (fst L) n) (α∈L' : ∀ i → α i ∈ L')
            → Cone (funcComp F (BDiag (λ i → α i , α∈L' i))) c → Cone (F* (⋁ α)) c
  coneOut (coneLemma c α α∈L' cc) ((u , u∈L') , u≤⋁α) = subst (λ x → C [ c , F .F-ob x ])
    (Σ≡Prop (λ x → L' x .snd) (sym p)) (isSheafF (λ i → β i , β∈L' i) ⋁β∈L' c ccβ .fst .fst)
    where
    β : FinVec (fst L) _
    β i = u ∧l α i
    β∈L' : ∀ i → β i ∈ L'
    β∈L' i = ∧lClosed _ _ u∈L' (α∈L' i)

    p : u ≡ ⋁ β
    p = sym (≤j→≤m _ _ u≤⋁α) ∙ ⋁Meetrdist _ _
    ⋁β∈L' : ⋁ β ∈ L'
    ⋁β∈L' = subst-∈ L' p u∈L'

    ccβ : Cone (funcComp F (BDiag (λ i → β i , β∈L' i))) c
    coneOut ccβ (sing i) = coneOut cc (sing i) ⋆⟨ C ⟩ F .F-hom (≤m→≤j _ _ (∧≤LCancel _ _))
    coneOut ccβ (pair i j i<j) = coneOut cc (pair i j i<j)
      ⋆⟨ C ⟩ F .F-hom ((≤m→≤j _ _ (≤-∧Pres _ _ _ _ (∧≤LCancel _ _) (∧≤LCancel _ _))))
    coneOutCommutes ccβ {u = u} idAr = cong (λ x → coneOut ccβ u ⋆⟨ C ⟩ x)
                                            (F-id (funcComp F (BDiag (λ i → β i , β∈L' i))))
                                     ∙ ⋆IdR C _
    coneOutCommutes ccβ (singPairL {i = i} {j} {i<j}) =
        coneOut cc (sing i) ⋆⟨ C ⟩ F .F-hom (≤m→≤j _ _ (∧≤LCancel _ _))
                            ⋆⟨ C ⟩ (funcComp F (BDiag (λ i → β i , β∈L' i)) .F-hom singPairL)
      ≡⟨ ⋆Assoc C _ _ _ ⟩
        coneOut cc (sing i) ⋆⟨ C ⟩ (F .F-hom (≤m→≤j _ _ (∧≤LCancel _ _))
                            ⋆⟨ C ⟩ (funcComp F (BDiag (λ i → β i , β∈L' i)) .F-hom singPairL))
      ≡⟨ cong (λ x → coneOut cc (sing i) ⋆⟨ C ⟩ x) (sym (F .F-seq _ _)) ⟩
        coneOut cc (sing i) ⋆⟨ C ⟩ F .F-hom
          (≤m→≤j _ _ (∧≤LCancel _ _)
            ⋆⟨ DLCat ^op ⟩ (BDiag (λ i → β i , β∈L' i) .F-hom (singPairL {i = i} {j} {i<j})))
      ≡⟨ cong (λ x → coneOut cc (sing i) ⋆⟨ C ⟩ F .F-hom
              {y = β i ∧l β j , ∧lClosed _ _ (β∈L' i) (β∈L' j)} x) (is-prop-valued _ _ _ _) ⟩
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
      ≡⟨ cong (λ x → x ⋆⟨ C ⟩ F .F-hom {y = β i ∧l β j , ∧lClosed _ _ (β∈L' i) (β∈L' j)}
               (≤m→≤j _ _ (≤-∧Pres _ _ _ _ (∧≤LCancel _ _) (∧≤LCancel _ _))))
               (coneOutCommutes cc (singPairL {i = i} {j} {i<j})) ⟩
        coneOut ccβ (pair i j i<j) ∎

    coneOutCommutes ccβ (singPairR {i = i} {j} {i<j}) =
        coneOut cc (sing j) ⋆⟨ C ⟩ F .F-hom (≤m→≤j _ _ (∧≤LCancel _ _))
                            ⋆⟨ C ⟩ (funcComp F (BDiag (λ i → β i , β∈L' i)) .F-hom singPairR)
      ≡⟨ ⋆Assoc C _ _ _ ⟩
        coneOut cc (sing j) ⋆⟨ C ⟩ (F .F-hom (≤m→≤j _ _ (∧≤LCancel _ _))
                            ⋆⟨ C ⟩ (funcComp F (BDiag (λ i → β i , β∈L' i)) .F-hom singPairR))
      ≡⟨ cong (λ x → coneOut cc (sing j) ⋆⟨ C ⟩ x) (sym (F .F-seq _ _)) ⟩
        coneOut cc (sing j) ⋆⟨ C ⟩ F .F-hom
          (≤m→≤j _ _ (∧≤LCancel _ _)
            ⋆⟨ DLCat ^op ⟩ (BDiag (λ i → β i , β∈L' i) .F-hom (singPairR {i = i} {j} {i<j})))
      ≡⟨ cong (λ x → coneOut cc (sing j) ⋆⟨ C ⟩ F .F-hom
              {y = β i ∧l β j , ∧lClosed _ _ (β∈L' i) (β∈L' j)} x) (is-prop-valued _ _ _ _) ⟩
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
      ≡⟨ cong (λ x → x ⋆⟨ C ⟩ F .F-hom {y = β i ∧l β j , ∧lClosed _ _ (β∈L' i) (β∈L' j)}
               (≤m→≤j _ _ (≤-∧Pres _ _ _ _ (∧≤LCancel _ _) (∧≤LCancel _ _))))
               (coneOutCommutes cc (singPairR {i = i} {j} {i<j})) ⟩
        coneOut ccβ (pair i j i<j) ∎

  coneOutCommutes (coneLemma c α α∈L' cc) {u = (u , u∈L') , u≤⋁α} {v = (v , v∈L') , v≤⋁α} u≥v = {!!}



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


  snd isDLSheafDLRan x y = {!!}

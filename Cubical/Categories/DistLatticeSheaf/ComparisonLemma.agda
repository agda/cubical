{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Categories.DistLatticeSheaf.ComparisonLemma where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
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

open import Cubical.Algebra.Semilattice
open import Cubical.Algebra.Lattice
open import Cubical.Algebra.DistLattice
open import Cubical.Algebra.DistLattice.Basis
open import Cubical.Algebra.DistLattice.BigOps

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Equivalence
open import Cubical.Categories.Limits.Limits
open import Cubical.Categories.Limits.Pullback
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.RightKan
open import Cubical.Categories.Instances.Poset
open import Cubical.Categories.Instances.Semilattice
open import Cubical.Categories.Instances.Lattice
open import Cubical.Categories.Instances.DistLattice
open import Cubical.Categories.Instances.Functors

open import Cubical.Categories.DistLatticeSheaf.Diagram
open import Cubical.Categories.DistLatticeSheaf.Base
open import Cubical.Categories.DistLatticeSheaf.Extension


private
  variable
    ℓ ℓ' ℓ'' : Level

module _ (L : DistLattice ℓ) (C : Category ℓ' ℓ'') (limitC : Limits {ℓ} {ℓ} C)
         (B : ℙ (fst L)) (isBasisB : IsBasis L B) where


 open Category hiding (_∘_)
 open Functor
 open NatTrans
 open Cone
 open LimCone
 open SheafOnBasis L C B isBasisB
 open PreSheafExtension L C limitC B

 open DistLatticeStr ⦃...⦄
 open JoinSemilattice (Lattice→JoinSemilattice (DistLattice→Lattice L))
 open PosetStr (IndPoset .snd) hiding (_≤_)
 open Join L


 private
  instance
   _ = snd L

  Lᵒᵖ = DistLatticeCategory L ^op
  Bᵒᵖ = ΣPropCat (DistLatticeCategory L) B ^op

  ShB = ΣPropCat (FUNCTOR Bᵒᵖ C) isDLBasisSheafProp
  ShL = ΣPropCat (FUNCTOR Lᵒᵖ C) (isDLSheafProp L C)

  i = baseIncl ^opF

 restPresSheafProp : ∀ (F : Functor Lᵒᵖ C) → isDLSheaf L C F → isDLBasisSheaf (F ∘F i)
 restPresSheafProp F isSheafF α ⋁α∈B =
   transport (λ i → isLimCone (diagPath i) (F .F-ob (⋁ α')) (limConesPathP i)) (isSheafF _ α')
   where
   open condCone α

   α' : FinVec (fst L) _
   α' i = α i .fst

   diagPath : F ∘F (FinVec→Diag L α') ≡ (F ∘F i) ∘F BDiag
   diagPath = Functor≡ diagPathOb diagPathHom
     where
     diagPathOb : ∀ c → (F ∘F (FinVec→Diag L α')) .F-ob c ≡ ((F ∘F i) ∘F BDiag) .F-ob c
     diagPathOb (sing i) = refl
     diagPathOb (pair i j i<j) = cong (F .F-ob) (∧lComm _ _)

     diagPathHom : ∀ {c} {d} f → PathP (λ i → C [ diagPathOb c i , diagPathOb d i ])
                                       ((F ∘F (FinVec→Diag L α')) .F-hom f)
                                       (((F ∘F i) ∘F BDiag) .F-hom f)
     diagPathHom {sing i} idAr = refl
     diagPathHom {pair i j i<j} idAr = functorCongP {F = F} (toPathP (is-prop-valued _ _ _ _))
     diagPathHom singPairL = functorCongP {F = F} (toPathP (is-prop-valued _ _ _ _))
     diagPathHom singPairR = functorCongP {F = F} (toPathP (is-prop-valued _ _ _ _))

   limConesPathP : PathP (λ i → Cone (diagPath i) (F .F-ob (⋁ α')))
                         (F-cone F (⋁Cone L α')) (F-cone (F ∘F i) (B⋁Cone ⋁α∈B))
   limConesPathP = conePathP limConesPathPOb
     where
     limConesPathPOb : ∀ c → PathP (λ i → C [ F .F-ob (⋁ α') , diagPath i .F-ob c ])
                                   (F-cone F (⋁Cone L α') .coneOut c)
                                   (F-cone (F ∘F i) (B⋁Cone ⋁α∈B) .coneOut c)
     limConesPathPOb (sing i) = refl
     limConesPathPOb (pair i j i<j) = functorCongP {F = F} (toPathP (is-prop-valued _ _ _ _))


 --restriction to basis as functor
 restSh : Functor ShL ShB
 restSh = ΣPropCatFunc (precomposeF C i) restPresSheafProp


 DLRanFun : Functor (FUNCTOR Bᵒᵖ C) (FUNCTOR Lᵒᵖ C)
 F-ob DLRanFun = DLRan
 N-ob (F-hom DLRanFun {x = F} {y = G} α) x = limOfArrows _ _ FLimCone GLimCone
   (λ u → α .N-ob (u .fst))
    λ e → sym (α .N-hom (e .fst))
   where
   FLimCone = limitC (_↓Diag limitC i F x) (T* limitC i F x)
   GLimCone = limitC (_↓Diag limitC i G x) (T* limitC i G x)
 N-hom (F-hom DLRanFun {x = F} {y = G} α) = {!!}
 F-id DLRanFun = {!!}
 F-seq DLRanFun = {!!}

 --extension of sheaves as functor
 extSh : Functor ShB ShL
 extSh = ΣPropCatFunc DLRanFun (isDLSheafDLRan isBasisB)

 open _≃ᶜ_ renaming (isEquiv to isEquivC)
 open isEquivalence

 DLComparisonLemma : ShB ≃ᶜ ShL
 func DLComparisonLemma = extSh
 invFunc (isEquivC DLComparisonLemma) = restSh
 η (isEquivC DLComparisonLemma) = {!!}
 ε (isEquivC DLComparisonLemma) = {!!}

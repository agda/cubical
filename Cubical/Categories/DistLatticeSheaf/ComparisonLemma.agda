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
open import Cubical.Categories.Morphism
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


 -- notation
 private module _ {F G : Functor Bᵒᵖ C} (α : NatTrans F G) (x : ob Lᵒᵖ) where
  theDiag = (_↓Diag limitC i F x)
  -- note that (_↓Diag limitC i F x) = (_↓Diag limitC i G x) definitionally
  FLimCone = limitC (_↓Diag limitC i F x) (T* limitC i F x)
  GLimCone = limitC (_↓Diag limitC i G x) (T* limitC i G x)

  ↓nt : NatTrans (T* limitC i F x) (T* limitC i G x)
  N-ob ↓nt u = α .N-ob (u .fst)
  N-hom ↓nt e = α .N-hom (e .fst)

  module _ (y : ob Lᵒᵖ) (x≥y : Lᵒᵖ [ x , y ]) where
   GYLimCone = limitC (_↓Diag limitC i G y) (T* limitC i G y)
   FYLimCone = limitC (_↓Diag limitC i F y) (T* limitC i F y)

   diagCone : Cone (T* limitC i G y) (RanOb limitC i F x)
   coneOut diagCone (u , y≥u) = limOut FLimCone (u , is-trans _ _ _ y≥u x≥y)
                                  ⋆⟨ C ⟩ α .N-ob u
   coneOutCommutes diagCone {u = (u , y≥u)} {v = (v , y≥v)} (u≥v , _) =
       (limOut FLimCone (u , is-trans _ _ _ y≥u x≥y) ⋆⟨ C ⟩ α .N-ob u) ⋆⟨ C ⟩ G .F-hom u≥v
     ≡⟨ ⋆Assoc C _ _ _ ⟩
       limOut FLimCone (u , is-trans _ _ _ y≥u x≥y) ⋆⟨ C ⟩ (α .N-ob u ⋆⟨ C ⟩ G .F-hom u≥v)
     ≡⟨ cong (seq' C (limOut FLimCone (u , is-trans _ _ _ y≥u x≥y))) (sym (α .N-hom u≥v)) ⟩
       limOut FLimCone (u , is-trans _ _ _ y≥u x≥y) ⋆⟨ C ⟩ (F .F-hom u≥v ⋆⟨ C ⟩ α .N-ob v)
     ≡⟨ sym (⋆Assoc C _ _ _) ⟩
       (limOut FLimCone (u , is-trans _ _ _ y≥u x≥y) ⋆⟨ C ⟩ F .F-hom u≥v) ⋆⟨ C ⟩ α .N-ob v
     ≡⟨ cong (λ x → x ⋆⟨ C ⟩ α .N-ob v) (limOutCommutes FLimCone (u≥v , is-prop-valued _ _ _ _)) ⟩
       limOut FLimCone (v , is-trans _ _ _ y≥v x≥y) ⋆⟨ C ⟩ α .N-ob v ∎
   diagArrow : C [ RanOb limitC i F x , RanOb limitC i G y ]
   diagArrow = limArrow GYLimCone _ diagCone



 DLRanFun : Functor (FUNCTOR Bᵒᵖ C) (FUNCTOR Lᵒᵖ C)
 F-ob DLRanFun = DLRan
 N-ob (F-hom DLRanFun α) x = limOfArrows (FLimCone α _) (GLimCone α _) (↓nt α x)
 N-hom (F-hom DLRanFun {x = F} {y = G} α) {x = x} {y = y} x≥y =
   sym (limArrowUnique (GLimCone α y) _ (diagCone α x y x≥y) _ isConeMorL)
     ∙ (limArrowUnique (GLimCone α y) _ _ _ isConeMorR)
   where
   l = limArrow (FLimCone α y) _ (RanCone limitC i F x≥y)
           ⋆⟨ C ⟩ limOfArrows (FLimCone α _) (GLimCone α _) (↓nt α y)

   isConeMorL : isConeMor (diagCone α x y x≥y) (limCone (GLimCone α y)) l
   isConeMorL (u , y≥u) =
       l ⋆⟨ C ⟩ (limOut (GLimCone α y) (u , y≥u))
     ≡⟨ ⋆Assoc C _ _ _ ⟩
       limArrow (FLimCone α y) _ (RanCone limitC i F x≥y)
         ⋆⟨ C ⟩ (limOfArrows (FLimCone α _) (GLimCone α _) (↓nt α y)
                   ⋆⟨ C ⟩ (limOut (GLimCone α y) (u , y≥u)))
     ≡⟨ cong (seq' C (limArrow (FLimCone α y) _ (RanCone limitC i F x≥y)))
             (limOfArrowsOut (FLimCone α _) (GLimCone α _) _ _) ⟩
       limArrow (FLimCone α y) _ (RanCone limitC i F x≥y)
         ⋆⟨ C ⟩ (limOut (FLimCone α _) (u , y≥u) ⋆⟨ C ⟩ α .N-ob u)
     ≡⟨ sym (⋆Assoc C _ _ _) ⟩
       (limArrow (FLimCone α y) _ (RanCone limitC i F x≥y)
         ⋆⟨ C ⟩ (limOut (FLimCone α _) (u , y≥u))) ⋆⟨ C ⟩ α .N-ob u
     ≡⟨ cong (λ x → x ⋆⟨ C ⟩ (α .N-ob u)) (limArrowCommutes (FLimCone α _) _ _ _) ⟩
       limOut (FLimCone α x) (u , is-trans _ _ _ y≥u x≥y) ⋆⟨ C ⟩ α .N-ob u ∎

   r = limOfArrows (FLimCone α _) (GLimCone α _) (↓nt α x)
           ⋆⟨ C ⟩ limArrow (GLimCone α y) _ (RanCone limitC i G x≥y)

   isConeMorR : isConeMor (diagCone α x y x≥y) (limCone (GLimCone α y)) r
   isConeMorR (u , y≥u) =
       r ⋆⟨ C ⟩ (limOut (GLimCone α y) (u , y≥u))
     ≡⟨ ⋆Assoc C _ _ _ ⟩
       limOfArrows (FLimCone α _) (GLimCone α _) (↓nt α x)
         ⋆⟨ C ⟩ (limArrow (GLimCone α y) _ (RanCone limitC i G x≥y)
                 ⋆⟨ C ⟩ (limOut (GLimCone α y) (u , y≥u)))
     ≡⟨ cong (seq' C (limOfArrows (FLimCone α _) (GLimCone α _) (↓nt α x)))
          (limArrowCommutes (GLimCone α _) _ _ _) ⟩
       limOfArrows (FLimCone α _) (GLimCone α _) (↓nt α x)
         ⋆⟨ C ⟩ limOut (GLimCone α x) (u , is-trans _ _ _ y≥u x≥y)
     ≡⟨ limOfArrowsOut (FLimCone α x) (GLimCone α x) _ _ ⟩
       limOut (FLimCone α x) (u , is-trans _ _ _ y≥u x≥y) ⋆⟨ C ⟩ α .N-ob u ∎


 F-id DLRanFun {x = F} = makeNatTransPath
                           (funExt λ x → limOfArrowsId (FLimCone (idTrans F) x))
 F-seq DLRanFun α β = makeNatTransPath
                        (funExt λ x → limOfArrowsSeq (FLimCone α x) (GLimCone α x)
                                                     (GLimCone β x) (↓nt α x) (↓nt β x))



 --extension of sheaves as functor
 extSh : Functor ShB ShL
 extSh = ΣPropCatFunc DLRanFun (isDLSheafDLRan isBasisB)

 open _≃ᶜ_ renaming (isEquiv to isEquivC)
 open isEquivalence
 open NatIso
 open isIso

 DLPShfEquiv : (FUNCTOR Bᵒᵖ C) ≃ᶜ (FUNCTOR Lᵒᵖ C)
 func DLPShfEquiv = DLRanFun
 invFunc (isEquivC DLPShfEquiv) = precomposeF C i
 -- the unit
 N-ob (trans (η (isEquivC DLPShfEquiv))) F = symNatIso (DLRanNatIso F) .trans
 N-hom (trans (η (isEquivC DLPShfEquiv))) {x = F} {y = G} α = makeNatTransPath (funExt
   λ u → invFlipSq (isIso→areInv (DLRanNatIso F .nIso u)) (isIso→areInv (DLRanNatIso G .nIso u))
                   (invSq u))
   where
   invSq : ∀ (u : ob Bᵒᵖ)
         → limOfArrows (FLimCone α (u .fst)) (GLimCone α _) (↓nt α (u .fst))
             ⋆⟨ C ⟩ limOut (GLimCone α (u .fst)) (u , is-trans _ _ _ (id Bᵒᵖ {u}) (id Bᵒᵖ {u}))
         ≡ limOut (FLimCone α (u .fst)) (u , is-trans _ _ _ (id Bᵒᵖ {u}) (id Bᵒᵖ {u}))
             ⋆⟨ C ⟩ α .N-ob u
   invSq u = limOfArrowsOut (FLimCone α (u .fst)) (GLimCone α (u .fst)) _ _
 nIso (η (isEquivC DLPShfEquiv)) F = NatIso→FUNCTORIso _ _ (symNatIso (DLRanNatIso F)) .snd

 -- the counit
 N-ob (trans (ε (isEquivC DLPShfEquiv))) F = {!DLRanUnivProp (F ∘F i) F (idTrans _) .fst .fst!}
 N-hom (trans (ε (isEquivC DLPShfEquiv))) = {!!}
 nIso (ε (isEquivC DLPShfEquiv)) = {!!}

 DLComparisonLemma : ShB ≃ᶜ ShL
 DLComparisonLemma = {!!}

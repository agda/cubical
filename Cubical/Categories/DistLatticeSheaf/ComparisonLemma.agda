{-

  This file contains a proof of the following fact:
  Given a distributive lattice L with a basis B ⊆ L,
  then the category of sheaves on B is equivalent to
  the category of sheaves on L.

  This is a special case of the comparison lemma as stated in e.g.
  https://ncatlab.org/nlab/show/comparison+lemma

-}

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

open import Cubical.Relation.Binary.Order.Poset
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.Semilattice
open import Cubical.Algebra.Lattice
open import Cubical.Algebra.DistLattice
open import Cubical.Algebra.DistLattice.Basis
open import Cubical.Algebra.DistLattice.BigOps

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Morphism
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Adjoint
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
 open Order (DistLattice→Lattice L)
 open MeetSemilattice (Lattice→MeetSemilattice (DistLattice→Lattice L))
      using (∧≤RCancel ; ∧≤LCancel)
 private
  instance
   _ = snd L

  Lᵒᵖ = DistLatticeCategory L ^op
  Bᵒᵖ = ΣPropCat (DistLatticeCategory L) B ^op

  SheafB = ΣPropCat (FUNCTOR Bᵒᵖ C) isDLBasisSheafProp
  SheafL = ΣPropCat (FUNCTOR Lᵒᵖ C) (isDLSheafProp L C)

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
 sheafRestriction : Functor SheafL SheafB
 sheafRestriction = ΣPropCatFunc (precomposeF C i) restPresSheafProp

 -- important lemma: a natural transformation between sheaves on L is an
 -- iso if the restriction to B is an iso. This will give us that
 -- that the unit of the comparison lemma is an iso and thus that
 -- restriction of sheaves is fully-faithful
 restIsoLemma : (F G : ob SheafL) (α : NatTrans (F .fst) (G .fst))
              → (∀ (u : ob Bᵒᵖ) → isIso C ((α ∘ˡ i) .N-ob u))
              →  ∀ (x : ob Lᵒᵖ) → isIso C (α .N-ob x)
 restIsoLemma (F , isSheafF) (G , isSheafG) α αiIso x =
   PT.rec (isPropIsIso _) basisHyp (isBasisB .⋁Basis x)
   where
   Fi = F ∘F i
   Gi = G ∘F i
   open NatIso
   αiNatIso : NatIso Fi Gi
   trans αiNatIso = α ∘ˡ i
   nIso αiNatIso = αiIso

   open IsBasis
   basisHyp : Σ[ n ∈ ℕ ] Σ[ u ∈ FinVec (L .fst) n ] (∀ j → u j ∈ B) × (⋁ u ≡ x)
            → isIso C (α .N-ob x)
   basisHyp (n , u , u∈B , ⋁u≡x) = transport (λ i → isIso C (q i)) (subst (isIso C) p αᵤ'IsIso)
     where
     open isIso

     FLimCone = isDLSheafLimCone L C F isSheafF n u
     GLimCone = isDLSheafLimCone L C G isSheafG n u

     uᴮ : FinVec (Bᵒᵖ .ob) n
     uᴮ i = u i , u∈B i

     uᴮDiag = condCone.BDiag uᴮ

     αi⁻¹ : (v : ob Bᵒᵖ) → C [ Gi .F-ob v , Fi .F-ob v ]
     αi⁻¹ v = αiIso v .inv

     σ : NatTrans (F ∘F (FinVec→Diag L u)) (G ∘F (FinVec→Diag L u))
     N-ob σ = α .N-ob ∘ FinVec→Diag L u .F-ob
     N-hom σ = α .N-hom ∘ FinVec→Diag L u .F-hom

     open SemilatticeStr ⦃...⦄
     instance _ = snd (Basis→MeetSemilattice L B isBasisB)

     σ⁻¹ : NatTrans (G ∘F (FinVec→Diag L u)) (F ∘F (FinVec→Diag L u))
     N-ob σ⁻¹ (sing i) = αi⁻¹ (uᴮDiag .F-ob (sing i))
     N-ob σ⁻¹ (pair i j i<j) = αi⁻¹ ((u j , u∈B j) · (u i , u∈B i))
                               -- (uᴮDiag .F-ob (pair i j i<j)) modulo swapping i and j
     N-hom σ⁻¹ (idAr {x = v}) =
       G .F-hom (id Lᵒᵖ) ⋆⟨ C ⟩ σ⁻¹ .N-ob v ≡⟨ cong (λ f → f ⋆⟨ C ⟩ σ⁻¹ .N-ob v) (G .F-id) ⟩
       id C ⋆⟨ C ⟩ σ⁻¹ .N-ob v              ≡⟨ ⋆IdL C _ ⟩
       σ⁻¹ .N-ob v                          ≡⟨ sym (⋆IdR C _) ⟩
       σ⁻¹ .N-ob v ⋆⟨ C ⟩ id C              ≡⟨ cong (λ f → σ⁻¹ .N-ob v ⋆⟨ C ⟩ f) (sym (F .F-id)) ⟩
       σ⁻¹ .N-ob v ⋆⟨ C ⟩ F .F-hom (id Lᵒᵖ) ∎
     N-hom σ⁻¹ (singPairL {i} {j} {i<j})  = transport (λ 𝕚 → p 𝕚 ≡ r 𝕚) q
       where
       p : PathP (λ 𝕚 → C [ G .F-ob (u i) , F .F-ob (fst (·Comm (u i , u∈B i) (u j , u∈B j) 𝕚)) ])
                 (G .F-hom (≤m→≤j _ _ (∧≤RCancel _ _)) ⋆⟨ C ⟩ αi⁻¹ (uᴮDiag .F-ob (pair i j i<j)))
                 (G .F-hom (≤m→≤j _ _ (∧≤LCancel _ _)) ⋆⟨ C ⟩ αi⁻¹ ((u j , u∈B j) · (u i , u∈B i)))
       p 𝕚 = G .F-hom (isProp→PathP (λ 𝕚' → is-prop-valued (∧lComm (u i) (u j) 𝕚') (u i))
                      (≤m→≤j _ _ (∧≤RCancel _ _)) (≤m→≤j _ _ (∧≤LCancel _ _)) 𝕚)
               ⋆⟨ C ⟩ αi⁻¹ (·Comm (u i , u∈B i) (u j , u∈B j) 𝕚)

       q : G .F-hom (≤m→≤j _ _ (∧≤RCancel _ _)) ⋆⟨ C ⟩ αi⁻¹ (uᴮDiag .F-ob (pair i j i<j))
         ≡ αi⁻¹ (u i , u∈B i) ⋆⟨ C ⟩ F .F-hom (≤m→≤j _ _ (∧≤RCancel _ _))
       q = sqLL αiNatIso

       r : PathP (λ 𝕚 → C [ G .F-ob (u i) , F .F-ob (fst (·Comm (u i , u∈B i) (u j , u∈B j) 𝕚)) ])
                 (αi⁻¹ (u i , u∈B i) ⋆⟨ C ⟩ F .F-hom (≤m→≤j _ _ (∧≤RCancel _ _)))
                 (αi⁻¹ (u i , u∈B i) ⋆⟨ C ⟩ F .F-hom (≤m→≤j _ _ (∧≤LCancel _ _)))
       r 𝕚 = αi⁻¹ (u i , u∈B i)
               ⋆⟨ C ⟩ F .F-hom (isProp→PathP (λ 𝕚' → is-prop-valued (∧lComm (u i) (u j) 𝕚') (u i))
                               (≤m→≤j _ _ (∧≤RCancel _ _)) (≤m→≤j _ _ (∧≤LCancel _ _)) 𝕚)

     N-hom σ⁻¹ (singPairR {i} {j} {i<j}) =  transport (λ 𝕚 → p 𝕚 ≡ r 𝕚) q
       where
       p : PathP (λ 𝕚 → C [ G .F-ob (u j) , F .F-ob (fst (·Comm (u i , u∈B i) (u j , u∈B j) 𝕚)) ])
                 (G .F-hom (≤m→≤j _ _ (∧≤LCancel _ _)) ⋆⟨ C ⟩ αi⁻¹ (uᴮDiag .F-ob (pair i j i<j)))
                 (G .F-hom (≤m→≤j _ _ (∧≤RCancel _ _)) ⋆⟨ C ⟩ αi⁻¹ ((u j , u∈B j) · (u i , u∈B i)))
       p 𝕚 = G .F-hom (isProp→PathP (λ 𝕚' → is-prop-valued (∧lComm (u i) (u j) 𝕚') (u j))
                      (≤m→≤j _ _ (∧≤LCancel _ _)) (≤m→≤j _ _ (∧≤RCancel _ _)) 𝕚)
               ⋆⟨ C ⟩ αi⁻¹ (·Comm (u i , u∈B i) (u j , u∈B j) 𝕚)

       q : G .F-hom (≤m→≤j _ _ (∧≤LCancel _ _)) ⋆⟨ C ⟩ αi⁻¹ (uᴮDiag .F-ob (pair i j i<j))
         ≡ αi⁻¹ (u j , u∈B j) ⋆⟨ C ⟩ F .F-hom (≤m→≤j _ _ (∧≤LCancel _ _))
       q = sqLL αiNatIso

       r : PathP (λ 𝕚 → C [ G .F-ob (u j) , F .F-ob (fst (·Comm (u i , u∈B i) (u j , u∈B j) 𝕚)) ])
                 (αi⁻¹ (u j , u∈B j) ⋆⟨ C ⟩ F .F-hom (≤m→≤j _ _ (∧≤LCancel _ _)))
                 (αi⁻¹ (u j , u∈B j) ⋆⟨ C ⟩ F .F-hom (≤m→≤j _ _ (∧≤RCancel _ _)))
       r 𝕚 = αi⁻¹ (u j , u∈B j)
               ⋆⟨ C ⟩ F .F-hom (isProp→PathP (λ 𝕚' → is-prop-valued (∧lComm (u i) (u j) 𝕚') (u j))
                               (≤m→≤j _ _ (∧≤LCancel _ _)) (≤m→≤j _ _ (∧≤RCancel _ _)) 𝕚)

     -- σ and σ⁻¹ are inverse:
     σσ⁻¹≡id : σ ●ᵛ σ⁻¹ ≡ idTrans _
     σσ⁻¹≡id = makeNatTransPath (funExt σσ⁻¹≡idOb)
       where
       σσ⁻¹≡idOb : ∀ x → σ .N-ob x ⋆⟨ C ⟩ σ⁻¹ .N-ob x ≡ id C
       σσ⁻¹≡idOb (sing i) = αiIso (u i , u∈B i) .ret
       σσ⁻¹≡idOb (pair i j i<j) = αiIso ((u j , u∈B j) · (u i , u∈B i)) .ret

     σ⁻¹σ≡id : σ⁻¹ ●ᵛ σ ≡ idTrans _
     σ⁻¹σ≡id = makeNatTransPath (funExt σ⁻¹σ≡idOb)
       where
       σ⁻¹σ≡idOb : ∀ x → σ⁻¹ .N-ob x ⋆⟨ C ⟩ σ .N-ob x ≡ id C
       σ⁻¹σ≡idOb (sing i) = αiIso (u i , u∈B i) .sec
       σ⁻¹σ≡idOb (pair i j i<j) = αiIso ((u j , u∈B j) · (u i , u∈B i)) .sec


     αᵤ' = limOfArrows FLimCone GLimCone σ
     αᵤ'⁻¹ = limOfArrows GLimCone FLimCone σ⁻¹

     αᵤ'IsIso : isIso C αᵤ'
     inv αᵤ'IsIso = αᵤ'⁻¹
     sec αᵤ'IsIso = sym (limOfArrowsSeq GLimCone FLimCone GLimCone σ⁻¹ σ)
                  ∙∙ cong (limOfArrows GLimCone GLimCone) σ⁻¹σ≡id
                  ∙∙ limOfArrowsId GLimCone
     ret αᵤ'IsIso = sym (limOfArrowsSeq FLimCone GLimCone FLimCone σ σ⁻¹)
                  ∙∙ cong (limOfArrows FLimCone FLimCone) σσ⁻¹≡id
                  ∙∙ limOfArrowsId FLimCone


     p : αᵤ' ≡ (α .N-ob (⋁ u))
     p = limArrowUnique GLimCone _ _ _
           (isConeMorSingLemma (limOfArrowsCone FLimCone σ) (F-cone G (⋁Cone L u))
             λ i → sym (α .N-hom (ind≤⋁ u i)))

     q : PathP (λ i → C [ F .F-ob (⋁u≡x i) , G .F-ob (⋁u≡x i) ]) (α .N-ob (⋁ u)) (α .N-ob x)
     q = cong (α .N-ob) ⋁u≡x


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
 sheafExtension : Functor SheafB SheafL
 sheafExtension = ΣPropCatFunc DLRanFun (isDLSheafDLRan isBasisB)



 open WeakInverse
 open NatIso
 open isIso

 DLComparisonLemma : SheafL ≃ᶜ SheafB
 DLComparisonLemma = record { func = sheafRestriction ; isEquiv = ∣ winv ∣₁}
   where
     winv : WeakInverse sheafRestriction
     invFunc winv = sheafExtension

     -- the unit is induced by the universal property
     N-ob (trans (η winv)) (F , _ ) =
       DLRanUnivProp (F ∘F i) F (idTrans _) .fst .fst
     N-hom (trans (η winv)) {x = (F , _)} {y = (G , _)} α =
       makeNatTransPath (funExt goal)
         where
         isConeMorComp : ∀ (x : ob Lᵒᵖ)
                       → isConeMor
                           ((NatTransCone _ _ _ F (idTrans _) x) ★ₙₜ (↓nt (α ∘ˡ i) x))
                             (GLimCone (α ∘ˡ i) _ .limCone)
                               (α .N-ob x
                                 ⋆⟨ C ⟩ limArrow (GLimCone (α ∘ˡ i) _) _
                                                 (NatTransCone _ _ _ G (idTrans _) x))
         isConeMorComp x u⇂@((u , u∈B) , u≤x) =
             α .N-ob x ⋆⟨ C ⟩ limArrow (GLimCone (α ∘ˡ i) _) _
                                       (NatTransCone _ _ _ G (idTrans _) x)
                       ⋆⟨ C ⟩ limOut (GLimCone (α ∘ˡ i) _) u⇂
           ≡⟨ ⋆Assoc C _ _ _ ⟩
             α .N-ob x ⋆⟨ C ⟩ (limArrow (GLimCone (α ∘ˡ i) _) _
                                        (NatTransCone _ _ _ G (idTrans _) x)
                                ⋆⟨ C ⟩ limOut (GLimCone (α ∘ˡ i) _) u⇂)
           ≡⟨ cong (λ y → α .N-ob x ⋆⟨ C ⟩ y) (limArrowCommutes (GLimCone (α ∘ˡ i) _) _ _ _) ⟩
             α .N-ob x ⋆⟨ C ⟩ (G .F-hom u≤x ⋆⟨ C ⟩ id C)
           ≡⟨ cong (λ y → α .N-ob x ⋆⟨ C ⟩ y) (⋆IdR C _) ⟩
             α .N-ob x ⋆⟨ C ⟩ G .F-hom u≤x
           ≡⟨ sym (α .N-hom u≤x) ⟩
             F .F-hom u≤x ⋆⟨ C ⟩ α .N-ob u
           ≡⟨ cong (λ x → x ⋆⟨ C ⟩ α .N-ob u) (sym (⋆IdR C _)) ⟩
             F .F-hom u≤x ⋆⟨ C ⟩ id C ⋆⟨ C ⟩ α .N-ob u ∎

         goal : ∀ (x : ob Lᵒᵖ)
              → α .N-ob x ⋆⟨ C ⟩ limArrow (GLimCone (α ∘ˡ i) _) _
                                          (NatTransCone _ _ _ G (idTrans _) x)
              ≡ limArrow (FLimCone (α ∘ˡ i) _) _
                         (NatTransCone _ _ _ F (idTrans _) x)
                   ⋆⟨ C ⟩ limOfArrows (FLimCone (α ∘ˡ i) _) (GLimCone (α ∘ˡ i) _)
                                      (↓nt (α ∘ˡ i) x)
         goal x = sym (limArrowUnique _ _ _ _ (isConeMorComp x))
                ∙ limArrowCompLimOfArrows _ _ _ _ _

     nIso (η winv) (F , isSheafF) = isIsoΣPropCat _ _ _
       (NatIso→FUNCTORIso _ _ σNatIso .snd)
       where
       σ = DLRanUnivProp (F ∘F i) F (idTrans _) .fst .fst

       σRestIso : isIso (FUNCTOR Bᵒᵖ C) (σ ∘ˡ i)
       inv σRestIso = DLRanNatTrans (F ∘F i)
       sec σRestIso = let ε = DLRanNatTrans (F ∘F i)
                          ε⁻¹ = NatIso→FUNCTORIso _ _ (DLRanNatIso (F ∘F i)) .snd .inv
         in ε ●ᵛ (σ ∘ˡ i)
          ≡⟨ cong (λ x → ε ●ᵛ x) (sym (⋆IdR (FUNCTOR Bᵒᵖ C) _)) ⟩
            ε ●ᵛ ((σ ∘ˡ i) ●ᵛ idTrans _)
          ≡⟨ cong (λ x → ε ●ᵛ ((σ ∘ˡ i) ●ᵛ x))
                  (sym (NatIso→FUNCTORIso _ _ (DLRanNatIso (F ∘F i)) .snd .ret)) ⟩
            ε ●ᵛ ((σ ∘ˡ i) ●ᵛ (ε ●ᵛ ε⁻¹))
          ≡⟨ cong (λ x → ε ●ᵛ x) (sym (⋆Assoc (FUNCTOR Bᵒᵖ C) _ _ _)) ⟩
            ε ●ᵛ ((σ ∘ˡ i) ●ᵛ ε ●ᵛ ε⁻¹)
          ≡⟨ cong (λ x → ε ●ᵛ (x ●ᵛ ε⁻¹))
                  (sym (DLRanUnivProp (F ∘F i) F (idTrans _) .fst .snd)) ⟩
            ε ●ᵛ (idTrans _ ●ᵛ ε⁻¹)
          ≡⟨ cong (λ x → ε ●ᵛ x) (⋆IdL (FUNCTOR Bᵒᵖ C) _) ⟩
            ε ●ᵛ ε⁻¹
          ≡⟨ NatIso→FUNCTORIso _ _ (DLRanNatIso (F ∘F i)) .snd .ret ⟩
            idTrans _ ∎
       ret σRestIso = sym (DLRanUnivProp (F ∘F i) F (idTrans _) .fst .snd)

       σNatIso : NatIso F (DLRan (F ∘F i))
       trans σNatIso = σ
       nIso σNatIso = restIsoLemma
                        (F , isSheafF)
                          (_ , isDLSheafDLRan isBasisB _ (restPresSheafProp _ isSheafF))
                            σ
                              (FUNCTORIso→NatIso _ _ (_ , σRestIso) .nIso)

     -- the counit is easy
     N-ob (trans (ε winv)) (F , _) = DLRanNatTrans F
     N-hom (trans (ε winv)) α = -- DLRanNatTrans F is functorial in F
       makeNatTransPath (funExt (λ u → limOfArrowsOut (FLimCone α (u .fst))
                                                      (GLimCone α (u .fst)) _ _))
     nIso (ε winv) (F , isSheafF) = isIsoΣPropCat _ _ _
       (NatIso→FUNCTORIso _ _ (DLRanNatIso F) .snd)


 -- useful corollary:
 -- if two natural transformations between sheaves agree on the basis they are identical
 makeNatTransPathRest : (F G : ob SheafL) (α β : NatTrans (F .fst) (G .fst))
                      → (∀ (u : ob Bᵒᵖ) → (α ∘ˡ i) .N-ob u ≡ (β ∘ˡ i) .N-ob u)
                      → α ≡ β
 makeNatTransPathRest F G _ _ basePaths = isFaithfulSheafRestriction F G _ _
                                            (makeNatTransPath (funExt basePaths))
   where
   isFaithfulSheafRestriction = isEquiv→Faithful (DLComparisonLemma ._≃ᶜ_.isEquiv)

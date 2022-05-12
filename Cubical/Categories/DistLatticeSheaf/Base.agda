{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.Categories.DistLatticeSheaf.Base where

open import Cubical.Foundations.Prelude
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

open import Cubical.Categories.Category
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

private
  variable
    ℓ ℓ' ℓ'' : Level


module PreSheafExtension (L : DistLattice ℓ) (C : Category ℓ' ℓ'')
                         (limitC : Limits {ℓ} {ℓ} C) (L' : ℙ (fst L)) where

 open Functor

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



module _ (L : DistLattice ℓ) (C : Category ℓ' ℓ'') (T : Terminal C) where
  open Category hiding (_⋆_)
  open Functor
  open Order (DistLattice→Lattice L)
  open DistLatticeStr (snd L)
  open JoinSemilattice (Lattice→JoinSemilattice (DistLattice→Lattice L))
  open MeetSemilattice (Lattice→MeetSemilattice (DistLattice→Lattice L))
      using (∧≤RCancel ; ∧≤LCancel)
  open PosetStr (IndPoset .snd) hiding (_≤_)

  𝟙 : ob C
  𝟙 = terminalOb C T

  private
   DLCat : Category ℓ ℓ
   DLCat = DistLatticeCategory L

  open Category DLCat

  -- C-valued presheaves on a distributive lattice
  DLPreSheaf : Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
  DLPreSheaf = Functor (DLCat ^op) C

  module _ (x y : L .fst)where
    hom-∨₁ : DLCat [ x , x ∨l y ]
    hom-∨₁ = ∨≤RCancel _ _

    hom-∨₂ : DLCat [ y , x ∨l y ]
    hom-∨₂ = ∨≤LCancel _ _

    hom-∧₁ : DLCat [ x ∧l y , x ]
    hom-∧₁ = ≤m→≤j _ _ (∧≤RCancel _ _)

    hom-∧₂ : DLCat [ x ∧l y , y ]
    hom-∧₂ = ≤m→≤j _ _ (∧≤LCancel _ _)


    {-
       x ∧ y ----→   x
         |           |
         |    sq     |
         V           V
         y   ----→ x ∨ y
    -}
    sq : hom-∧₂ ⋆ hom-∨₂ ≡ hom-∧₁ ⋆ hom-∨₁
    sq = is-prop-valued (x ∧l y) (x ∨l y) (hom-∧₂ ⋆ hom-∨₂) (hom-∧₁ ⋆ hom-∨₁)

    {-
      F(x ∨ y) ----→ F(x)
         |            |
         |     Fsq    |
         V            V
        F(y) ------→ F(x ∧ y)
    -}
    Fsq : (F : DLPreSheaf)
        → F .F-hom hom-∨₂ ⋆⟨ C ⟩ F .F-hom hom-∧₂ ≡
          F .F-hom hom-∨₁ ⋆⟨ C ⟩ F .F-hom hom-∧₁
    Fsq F = F-square F sq

  isDLSheafPullback : (F : DLPreSheaf) → Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
  isDLSheafPullback F = (F-ob F 0l ≡ 𝟙)
                      × ((x y : L .fst) → isPullback C _ _ _ (Fsq x y F))

  -- TODO: might be better to define this as a record
  DLSheafPullback : Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
  DLSheafPullback = Σ[ F ∈ DLPreSheaf ] isDLSheafPullback F


  -- Now for the proper version using limits of the right kind:
  open Join L
  isDLSheaf : (F : DLPreSheaf) → Type _
  isDLSheaf F = ∀ (n : ℕ) (α : FinVec (fst L) n) → isLimCone _ _ (F-cone F (⋁Cone L α))
  --TODO: Equivalence of isDLSheaf and isDLSheafPullback



module SheafOnBasis (L : DistLattice ℓ) (C : Category ℓ' ℓ'') (T : Terminal C)
                    (L' : ℙ (fst L)) (hB : IsBasis L L') where

 open Category
 open Functor

 open DistLatticeStr ⦃...⦄
 open SemilatticeStr ⦃...⦄
 open IsBasis hB

 private
  DLCat = DistLatticeCategory L
  BasisCat = ΣPropCat  DLCat L'
  DLBasisPreSheaf = Functor (BasisCat ^op) C

  -- to avoid writing 𝟙 L C T
  1c : ob C
  1c = terminalOb C T

  instance
   _ = snd L
   _ = snd (Basis→MeetSemilattice L L' hB)


 module condSquare (x y : ob BasisCat) (x∨y∈L' : fst x ∨l fst y ∈ L') where

  private
   x∨y : ob BasisCat -- = Σ[ x ∈ L ] (x ∈ L')
   x∨y = fst x ∨l fst y , x∨y∈L'

  {-
     x ∧ y ----→   x
       |           |
       |    sq     |
       V           V
       y   ----→ x ∨ y

     but as a square in BasisCat
  -}
  Bsq : seq' BasisCat {x = x · y} {y = y} {z = x∨y} (hom-∧₂ L C T (fst x) (fst y))
                                                    (hom-∨₂ L C T (fst x) (fst y))
      ≡ seq' BasisCat {x = x · y} {y = x} {z = x∨y} (hom-∧₁ L C T (fst x) (fst y))
                                                    (hom-∨₁ L C T (fst x) (fst y))
  Bsq = sq L C T (fst x) (fst y)

  {-
    F(x ∨ y) ----→ F(x)
       |            |
       |     Fsq    |
       V            V
      F(y) ------→ F(x ∧ y)

    square in C but now F is only presheaf on BasisCat
  -}
  BFsq : (F : DLBasisPreSheaf)
       → seq' C {x = F .F-ob x∨y} {y = F .F-ob y} {z = F .F-ob (x · y)}
                (F .F-hom (hom-∨₂ L C T (fst x) (fst y)))
                (F .F-hom (hom-∧₂ L C T (fst x) (fst y)))
       ≡ seq' C {x = F .F-ob x∨y} {y = F .F-ob x} {z = F .F-ob (x · y)}
                (F .F-hom (hom-∨₁ L C T (fst x) (fst y)))
                (F .F-hom (hom-∧₁ L C T (fst x) (fst y)))
  BFsq F = F-square F Bsq


 -- On a basis this is weaker than the definition below!
 isDLBasisSheafPullback : DLBasisPreSheaf → Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
 isDLBasisSheafPullback F = ((0∈L' : 0l ∈ L') → F .F-ob (0l , 0∈L') ≡ 1c)
                          × ((x y : ob BasisCat) (x∨y∈L' : fst x ∨l fst y ∈ L')
                               → isPullback C _ _ _ (BFsq x y x∨y∈L' F))
                                 where open condSquare

 DLBasisSheafPullback : Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
 DLBasisSheafPullback = Σ[ F ∈ DLBasisPreSheaf ] isDLBasisSheafPullback F


 -- the correct defintion
 open Join L
 module condCone {n : ℕ} (α : FinVec (ob BasisCat) n) (⋁α∈L' : ⋁ (λ i →  α i .fst) ∈ L') where
   open JoinSemilattice (Lattice→JoinSemilattice (DistLattice→Lattice L))
   open PosetStr (IndPoset .snd) hiding (_≤_)
   open MeetSemilattice (Lattice→MeetSemilattice (DistLattice→Lattice L))
        using (∧≤RCancel ; ∧≤LCancel)
   open Order (DistLattice→Lattice L)
   open Cone
   private
     α' : FinVec (fst L) n
     α' i = α i .fst
     ⋁α : ob BasisCat
     ⋁α = ⋁ α' , ⋁α∈L'

   BDiag : Functor (DLShfDiag n) (BasisCat ^op)
   F-ob BDiag (sing i) = α i
   F-ob BDiag (pair i j _) = α i · α j -- α i ∧ α j + basis is closed under ∧
   F-hom BDiag idAr = is-refl _
   F-hom BDiag singPairL = ≤m→≤j _ _ (∧≤RCancel _ _)
   F-hom BDiag singPairR = ≤m→≤j _ _ (∧≤LCancel _ _)
   F-id BDiag = is-prop-valued _ _ _ _
   F-seq BDiag _ _ = is-prop-valued _ _ _ _

   B⋁Cone : Cone BDiag ⋁α
   coneOut B⋁Cone (sing i) = ind≤⋁ α' i
   coneOut B⋁Cone (pair i _ _) = is-trans _ (α' i) _ (≤m→≤j _ _ (∧≤RCancel _ _)) (ind≤⋁ α' i)
   coneOutCommutes B⋁Cone _ = is-prop-valued _ _ _ _

 isDLBasisSheaf : DLBasisPreSheaf → Type _
 isDLBasisSheaf F = ∀ {n : ℕ} (α : FinVec (ob BasisCat) n) (⋁α∈L' : ⋁ (λ i →  α i .fst) ∈ L')
                  → isLimCone _ _ (F-cone F (B⋁Cone  α ⋁α∈L'))
                    where open condCone





  -- To prove the statement we probably need that C is:
  -- 1. univalent
  -- 2. has finite limits (or pullbacks and a terminal object)
  -- 3. isGroupoid (C .ob)
  -- The last point is not strictly necessary, but we have to have some
  -- control over the hLevel as we want to write F(x) in terms of its
  -- basis cover which is information hidden under a prop truncation...
  -- Alternatively we just prove the statement for C = CommRingsCategory

  -- TODO: is unique existence expressed like this what we want?
  -- statement : (F' : DLBasisSheaf)
  --           → ∃![ F ∈ DLSheaf L C T ] ((x : fst L) → (x ∈ L') → CatIso C (F-ob (fst F) x) (F-ob (fst F') x)) -- TODO: if C is univalent the CatIso could be ≡?
  -- statement (F' , h1 , hPb) = ?

  -- It might be easier to prove all of these if we use the definition
  -- in terms of particular limits instead





  -- Scrap zone:

  -- -- Sublattices: upstream later
  -- record isSublattice (L' : ℙ (fst L)) : Type ℓ where
  --   field
  --     1l-closed  : 1l ∈ L'
  --     0l-closed  : 0l ∈ L'
  --     ∧l-closed  : {x y : fst L} → x ∈ L' → y ∈ L' → x ∧l y ∈ L'
  --     ∨l-closed  : {x y : fst L} → x ∈ L' → y ∈ L' → x ∨l y ∈ L'

  -- open isSublattice

  -- Sublattice : Type (ℓ-suc ℓ)
  -- Sublattice = Σ[ L' ∈ ℙ (fst L) ] isSublattice L'

  -- restrictDLSheaf : DLSheaf → Sublattice → DLSheaf
  -- F-ob (fst (restrictDLSheaf F (L' , HL'))) x = {!F-ob (fst F) x!} -- Hmm, not nice...
  -- F-hom (fst (restrictDLSheaf F L')) = {!!}
  -- F-id (fst (restrictDLSheaf F L')) = {!!}
  -- F-seq (fst (restrictDLSheaf F L')) = {!!}
  -- snd (restrictDLSheaf F L') = {!!}

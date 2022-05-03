{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.Categories.DistLatticeSheaf where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset
open import Cubical.Data.Sigma

open import Cubical.Relation.Binary.Poset

open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Semilattice
open import Cubical.Algebra.Lattice
open import Cubical.Algebra.DistLattice
open import Cubical.Algebra.DistLattice.Basis

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

  hom-∨₁ : (x y : L .fst) → DLCat [ x , x ∨l y ]
  hom-∨₁ = ∨≤RCancel
    -- TODO: isn't the fixity of the operators a bit weird?

  hom-∨₂ : (x y : L .fst) → DLCat [ y , x ∨l y ]
  hom-∨₂ = ∨≤LCancel

  hom-∧₁ : (x y : L .fst) → DLCat [ x ∧l y , x ]
  hom-∧₁ _ _ = (≤m→≤j _ _ (∧≤RCancel _ _))

  hom-∧₂ : (x y : L .fst) → DLCat [ x ∧l y , y ]
  hom-∧₂ _ _ = (≤m→≤j _ _ (∧≤LCancel _ _))


  {-
     x ∧ y ----→   x
       |           |
       |    sq     |
       V           V
       y   ----→ x ∨ y
  -}
  sq : (x y : L .fst) → hom-∧₂ x y ⋆ hom-∨₂ x y ≡ hom-∧₁ x y ⋆ hom-∨₁ x y
  sq x y = is-prop-valued (x ∧l y) (x ∨l y) (hom-∧₂ x y ⋆ hom-∨₂ x y) (hom-∧₁ x y ⋆ hom-∨₁ x y)

  {-
    F(x ∨ y) ----→ F(x)
       |            |
       |     Fsq    |
       V            V
      F(y) ------→ F(x ∧ y)
  -}
  Fsq : (F : DLPreSheaf) (x y : L .fst)
      → F .F-hom (hom-∨₂ x y) ⋆⟨ C ⟩ F .F-hom (hom-∧₂ x y) ≡
        F .F-hom (hom-∨₁ x y) ⋆⟨ C ⟩ F .F-hom (hom-∧₁ x y)
  Fsq F x y = F-square F (sq x y)

  isDLSheaf : (F : DLPreSheaf) → Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
  isDLSheaf F = (F-ob F 0l ≡ 𝟙)
              × ((x y : L .fst) → isPullback C _ _ _ (Fsq F x y))

  -- TODO: might be better to define this as a record
  DLSheaf : Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
  DLSheaf = Σ[ F ∈ DLPreSheaf ] isDLSheaf F



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


 -- TODO: check that this is equivalent to the functor
 -- preserving terminal objects and pullbacks
 isDLBasisSheaf : DLBasisPreSheaf → Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
 isDLBasisSheaf F = ((0∈L' : 0l ∈ L') → F .F-ob (0l , 0∈L') ≡ 1c)
                  × ((x y : ob BasisCat) (x∨y∈L' : fst x ∨l fst y ∈ L')
                  → isPullback C _ _ _ (BFsq x y x∨y∈L' F))
  where
  open condSquare

  DLBasisSheaf : Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
  DLBasisSheaf = Σ[ F ∈ DLBasisPreSheaf ] isDLBasisSheaf F

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

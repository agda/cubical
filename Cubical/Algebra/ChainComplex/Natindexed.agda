{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Algebra.ChainComplex.Natindexed where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat
open import Cubical.Data.Fin
open import Cubical.Data.Sigma
open import Cubical.Data.Nat.Order
open import Cubical.Data.Empty as ⊥


open import Cubical.Structures.Successor
open import Cubical.Algebra.ChainComplex.Base

open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties

open import Cubical.Relation.Nullary


private variable
  ℓ : Level


-- Nat indexed chain complexes
module CCℕ = CC ℕ+Inj

-- Restriction of ℕ indexed chain complexes to Fin n indexed ones
module _ (n : ℕ) where
  open CC

  -- Fin n indexed chain complexes
  module CCFin = CC (Fin+Inj n)

  open ChainComplex
  open ChainComplexMap
  open ChainHomotopy

  ChainComplex→finChainComplex : CCℕ.ChainComplex ℓ → CCFin.ChainComplex ℓ
  chain (ChainComplex→finChainComplex C) i p = chain C (fst i) ≠suc
  bdry (ChainComplex→finChainComplex C) (i , zero , q) p = ⊥.rec (p refl)
  bdry (ChainComplex→finChainComplex C) (i , suc diff , q) p = bdry C i ≠suc
  bdry²=0 (ChainComplex→finChainComplex C) (i , zero , q) p = ⊥.rec (p refl)
  bdry²=0 (ChainComplex→finChainComplex C) (i , suc zero , q) p = ⊥.rec (p refl)
  bdry²=0 (ChainComplex→finChainComplex C) (i , suc (suc diff) , q) p = bdry²=0 C i ≠suc

  ChainComplexMap→finChainComplexMap : {C D : CCℕ.ChainComplex ℓ}
    → CCℕ.ChainComplexMap C D
    → CCFin.ChainComplexMap (ChainComplex→finChainComplex C)
                             (ChainComplex→finChainComplex D)
  chainmap (ChainComplexMap→finChainComplexMap ϕ) (x , zero , q) p = ⊥.rec (p refl)
  chainmap (ChainComplexMap→finChainComplexMap ϕ) (x , suc diff , q) _ = chainmap ϕ x _
  bdrycomm (ChainComplexMap→finChainComplexMap ϕ) (x , zero , q) p = ⊥.rec (p refl)
  bdrycomm (ChainComplexMap→finChainComplexMap ϕ) (x , suc zero , q) p = ⊥.rec (p refl)
  bdrycomm (ChainComplexMap→finChainComplexMap ϕ) (x , suc (suc diff) , p) q = bdrycomm ϕ x _
  
  chainHom→ : {C D : CCℕ.ChainComplex ℓ} (f g : CCℕ.ChainComplexMap C D)
    → CCℕ.ChainHomotopy f g
    → CCFin.ChainHomotopy
         (ChainComplexMap→finChainComplexMap f)
         (ChainComplexMap→finChainComplexMap g)
  htpy (chainHom→ f g h) (x , zero , q) p = ⊥.rec (p refl)
  htpy (chainHom→ f g h) (x , suc zero , q) p = ⊥.rec (p refl)
  htpy (chainHom→ f g h) (x , suc (suc diff) , q) p = htpy h x _
  bdryhtpy (chainHom→ f g h) (x , zero , q) p = ⊥.rec (p refl)
  bdryhtpy (chainHom→ f g h) (x , suc zero , q) p = ⊥.rec (p refl)
  bdryhtpy (chainHom→ f g h) (x , suc (suc zero) , q) p = ⊥.rec (p refl)
  bdryhtpy (chainHom→ f g h) (x , suc (suc (suc diff)) , q) _ = bdryhtpy h x _

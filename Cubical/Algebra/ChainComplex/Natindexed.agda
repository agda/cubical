{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Algebra.ChainComplex.Natindexed where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat
open import Cubical.Data.Fin
open import Cubical.Data.Sigma


open import Cubical.Structures.Successor
open import Cubical.Algebra.ChainComplex.Base

open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties



private variable
  ℓ : Level

-- Nat indexed chain complexes
module CCℕ = CC ℕ+

-- Restriction of ℕ indexed chain complexes to Fin n indexed ones
module _ (n : ℕ) where
  open CC

  module CCFin = CC (Fin+ n)

  open ChainComplex
  open ChainComplexMap
  open ChainHomotopy

  ChainComplex→finChainComplex : CCℕ.ChainComplex ℓ → CCFin.ChainComplex ℓ
  chain (ChainComplex→finChainComplex C) (x , zero , p) = trivialAbGroup
  chain (ChainComplex→finChainComplex C) (x , suc diff , p) = chain C x
  bdry (ChainComplex→finChainComplex C) (x , zero , p) = trivGroupHom
  bdry (ChainComplex→finChainComplex C) (x , suc zero , p) = trivGroupHom
  bdry (ChainComplex→finChainComplex C) (x , suc (suc diff) , p) = bdry C x
  bdry²=0 (ChainComplex→finChainComplex C) (x , zero , p) =
    Σ≡Prop (λ _ → isPropIsGroupHom _ _) refl
  bdry²=0 (ChainComplex→finChainComplex C) (x , suc zero , p) =
    Σ≡Prop (λ _ → isPropIsGroupHom _ _) refl
  bdry²=0 (ChainComplex→finChainComplex C) (x , suc (suc zero) , p) =
    Σ≡Prop (λ _ → isPropIsGroupHom _ _)
      (funExt λ y → IsGroupHom.pres1 (snd  (bdry C x)))
  bdry²=0 (ChainComplex→finChainComplex C) (x , suc (suc (suc diff)) , p) = bdry²=0 C x

  ChainComplexMap→finChainComplexMap : {C D : CCℕ.ChainComplex ℓ}
    → CCℕ.ChainComplexMap C D
    → CCFin.ChainComplexMap (ChainComplex→finChainComplex C)
                             (ChainComplex→finChainComplex D)
  chainmap (ChainComplexMap→finChainComplexMap
    record { chainmap = chainmap ; bdrycomm = bdrycomm }) (x , zero , p) = trivGroupHom
  chainmap (ChainComplexMap→finChainComplexMap
    record { chainmap = chainmap ; bdrycomm = bdrycomm }) (x , suc diff , p) = chainmap x
  bdrycomm (ChainComplexMap→finChainComplexMap
    record { chainmap = chainmap ; bdrycomm = bdrycomm }) (x , zero , p) = refl
  bdrycomm (ChainComplexMap→finChainComplexMap
    record { chainmap = chainmap ; bdrycomm = bdrycomm }) (x , suc zero , p) =
      Σ≡Prop (λ _ → isPropIsGroupHom _ _)
        (funExt λ c → sym (IsGroupHom.pres1 (chainmap x .snd)))
  bdrycomm (ChainComplexMap→finChainComplexMap
    record { chainmap = chainmap ; bdrycomm = bdrycomm }) (x , suc (suc diff) , p) = bdrycomm x

  chainHom→ : {C D : CCℕ.ChainComplex ℓ} (f g : CCℕ.ChainComplexMap C D)
    → CCℕ.ChainHomotopy f g
    → CCFin.ChainHomotopy
         (ChainComplexMap→finChainComplexMap f)
         (ChainComplexMap→finChainComplexMap g)  
  ChainHomotopy.htpy (chainHom→ f g
    record { htpy = htpy ; bdryhtpy = bdryhtpy }) (x , zero , q) = trivGroupHom
  ChainHomotopy.htpy (chainHom→ f g p) (x , suc zero , q) = trivGroupHom
  ChainHomotopy.htpy (chainHom→ f g p) (x , suc (suc diff) , q) = htpy p x
  bdryhtpy (chainHom→ f g p) (x , zero , q) = refl
  bdryhtpy (chainHom→ f g p) (x , suc zero , q) = refl
  bdryhtpy (chainHom→ f g p) (x , suc (suc zero) , q) = {!bdryhtpy p x!}
  bdryhtpy (chainHom→ f g p) (x , suc (suc (suc diff)) , q) = bdryhtpy p x

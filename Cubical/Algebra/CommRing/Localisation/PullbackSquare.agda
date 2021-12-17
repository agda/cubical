{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.Algebra.CommRing.Localisation.PullbackSquare where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Transport
open import Cubical.Functions.FunExtEquiv

import Cubical.Data.Empty as ⊥
open import Cubical.Data.Bool
open import Cubical.Data.Nat renaming ( _+_ to _+ℕ_ ; _·_ to _·ℕ_
                                      ; +-comm to +ℕ-comm ; +-assoc to +ℕ-assoc
                                      ; ·-assoc to ·ℕ-assoc ; ·-comm to ·ℕ-comm)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Vec
open import Cubical.Data.Sigma.Base
open import Cubical.Data.Sigma.Properties
open import Cubical.Data.FinData
open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary

open import Cubical.Algebra.Group
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Localisation.Base
open import Cubical.Algebra.CommRing.Localisation.UniversalProperty
open import Cubical.Algebra.CommRing.Localisation.InvertingElements
open import Cubical.Algebra.RingSolver.Reflection

open import Cubical.HITs.SetQuotients as SQ
open import Cubical.HITs.PropositionalTruncation as PT

open Iso

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ

module _ (R' : CommRing ℓ) (f g : (fst R')) where
 open IsRingHom
 open isMultClosedSubset
 open CommRingTheory R'
 open RingTheory (CommRing→Ring R')
 open Exponentiation R'
 open InvertingElementsBase R'

 open CommRingStr ⦃...⦄
 private
  R = R' .fst
  instance
   _ = R' .snd
   _ = R[1/ f ]AsCommRing .snd
   _ = R[1/ g ]AsCommRing .snd
   _ = R[1/ (R' .snd .CommRingStr._·_ f g) ]AsCommRing .snd

 open S⁻¹RUniversalProp R' [ f ⁿ|n≥0] (powersFormMultClosedSubset f)
      renaming (_/1 to _/1ᶠ)
 open S⁻¹RUniversalProp R' [ g ⁿ|n≥0] (powersFormMultClosedSubset g)
      renaming (_/1 to _/1ᵍ)
 open S⁻¹RUniversalProp R' [ (f · g) ⁿ|n≥0] (powersFormMultClosedSubset (f · g))


 injectivityLemma : ∀ (x : R) → x /1ᶠ ≡ 0r → x /1ᵍ ≡ 0r → x ≡ 0r
 injectivityLemma x = {!!}

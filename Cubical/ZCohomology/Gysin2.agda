{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.ZCohomology.Gysin2 where

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.Groups.Connected
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.Groups.Wedge
open import Cubical.ZCohomology.Properties
open import Cubical.ZCohomology.MayerVietorisUnreduced
open import Cubical.ZCohomology.Groups.Unit
open import Cubical.ZCohomology.Groups.Sn
open import Cubical.ZCohomology.RingStructure.CupProduct
open import Cubical.ZCohomology.RingStructure.RingLaws
open import Cubical.ZCohomology.RingStructure.GradedCommutativity

open import Cubical.Data.Sum
open import Cubical.Relation.Nullary

open import Cubical.Functions.Embedding

open import Cubical.Data.Fin

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Function hiding (case_of_)
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Pointed.Homogeneous

open import Cubical.Foundations.Univalence

open import Cubical.Relation.Nullary

open import Cubical.Data.Empty renaming (rec to ⊥-rec)
open import Cubical.Data.Sigma
open import Cubical.Data.Int hiding (_+'_)
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Algebra.Group
  renaming (ℤ to ℤGroup ; Unit to UnitGroup) hiding (Bool)

open import Cubical.HITs.Pushout.Flattening
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.EilenbergSteenrod
open import Cubical.HITs.Pushout
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp
open import Cubical.HITs.S1 renaming (_·_ to _*_)
open import Cubical.HITs.Truncation
  renaming (rec to trRec ; elim to trElim ; elim2 to trElim2 ; map to trMap)
open import Cubical.HITs.SetTruncation
  renaming (rec to sRec ; rec2 to sRec2 ; elim to sElim ; elim2 to sElim2 ; elim3 to sElim3 ; map to sMap)
open import Cubical.HITs.PropositionalTruncation
  renaming (rec to pRec ; elim to pElim)

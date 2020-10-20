{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Papers.HigherGroupsViaDURG where

-- Johannes Schipp von Branitz,
-- "Higher Groups via Displayed Univalent Reflexive Graphs in Cubical Type Theory".

import Cubical.Core.Glue as Glue

import Cubical.Data.Sigma.Properties as Sigma
import Cubical.Data.Unit as Unit

import Cubical.Foundations.GroupoidLaws as GroupoidLaws
import Cubical.Foundations.Equiv as Equiv
import Cubical.Foundations.Filler as Filler
import Cubical.Foundations.HLevels as HLevels
import Cubical.Foundations.HLevels' as HLevels'
import Cubical.Foundations.Isomorphism as Isomorphism
import Cubical.Foundations.Prelude as Prelude
import Cubical.Foundations.Path as FPath
import Cubical.Foundations.Univalence as Univalence
import Cubical.Foundations.Transport as Transport

import Cubical.Functions.FunExtEquiv as FunExtEquiv

import Cubical.Homotopy.Base as HomotopyBase
import Cubical.Homotopy.Connected as Connected

import Cubical.Structures.Subtype as Subtype

import Cubical.HITs.Truncation as Truncation

----------------------------------------------------------------------------
-- 2.  Cubical Type Theory
-- 2.1 Dependent Type Theory
-- 2.2 Path Types
-- 2.3 Cubical Groupoid Laws
-- 2.4 Functions, Equivalences and Univalence
-- 2.5 Truncated and Connected Types
-- 2.6 Groups
----------------------------------------------------------------------------


-- 2.2 Path Types


-- Example 2.1
open Sigma using (ΣPath≡PathΣ) public

open Prelude using (transport) public

-- Proposition 2.2
open FPath using (PathP≡Path) public


-- 2.3 Cubical Groupoid Laws

open Prelude using (refl;
                   transportRefl;
                   subst;
                   J) public
             renaming (cong to ap) public
open Prelude using (_∙∙_∙∙_;
                   doubleCompPath-filler;
                   compPath-unique) public
open Prelude using (_∙_) public

-- Lemma 2.5
open FPath using (PathP≡doubleCompPathˡ) public

-- Lemma 2.5
open GroupoidLaws using (doubleCompPath-elim) public

-- Lemma 2.6
open Filler using (cube-cong) public


-- 2.4 Functions, Equivalences and Univalence


open Unit renaming (Unit to 𝟙) public
open Prelude using (isContr) public
open Unit using (isContrUnit) public

-- Proposition 2.7
open Prelude using (singl;
                   isContrSingl) public

-- Definition 2.8
open Equiv renaming (fiber to fib) public
open Glue using (isEquiv;
                _≃_;
                equivFun) public
open Isomorphism using (Iso) public

-- Proposition 2.9
open Transport using (isEquivTransport) public

-- Proposition 2.10
open Sigma using (Σ-cong-equiv) public

-- Definition 2.11
open HomotopyBase using (_∼_) public

-- Theorem 2.12
open FunExtEquiv using (funExtEquiv) public

-- Theorem 2.13
open Univalence using (univalence) public
                renaming (ua to idToEquiv⁻¹;
                          uaβ to idToEquiv-β;
                          uaη to idToEquiv-η) public

-- Lemma 2.14
open Univalence using (ua→) public


-- 2.5 Truncated and Connected Types


open Prelude using (isProp;
                   isSet) public
open HLevels using (isOfHLevel;
                   TypeOfHLevel) public

-- Lemma 2.15
open Sigma using (Σ-contractFst;
                 Σ-contractSnd) public

-- Lemma 2.16
open Prelude using (isProp→PathP) public

-- Lemma 2.17
open Subtype using (subtypeWitnessIrrelevance) public
open Sigma using (Σ≡Prop) public

-- Definition 2.18
open HLevels using (isOfHLevelDep) public

-- Proposition 2.19
open HLevels' using (truncSelfId→truncId) public

-- Proposition 2.20
open HLevels using (isOfHLevelΣ) public

-- Proposition 2.21
open HLevels using (isPropIsOfHLevel) public

-- Proposition 2.22
open HLevels using (isOfHLevelΠ) public

-- Theorem 2.23
open Truncation using (∥_∥_;
                      rec;
                      elim) public

-- Definition 2.24
open Connected using (isConnected;
                     isConnectedFun) public

-- Lemma 2.25
open Connected using (isConnectedPoint) public





-- 2.6 Groups


-----------------------------------------------------------------------------
-- 3.  Displayed Structures
-- 3.1 Motivation
-- 3.2 Displayed Categories
-- 3.3 Univalent Reflexive Graphs
-- 3.4 Displayed Univalent Reflexive Graphs
-- 3.5 Operations on Displayed Univalent Reflexive Graphs
-- 3.6 Constructing Equivalences Using Displayed Univalent Reflexive Graphs
-----------------------------------------------------------------------------

-- 3.1 Motivation
-- 3.2 Displayed Categories
-- 3.3 Univalent Reflexive Graphs
-- 3.4 Displayed Univalent Reflexive Graphs
-- 3.5 Operations on Displayed Univalent Reflexive Graphs
-- 3.6 Constructing Equivalences Using Displayed Univalent Reflexive Graphs


-----------------------------------------------------------------------------
-- 4.  Equivalence of Strict 2-Groups and Crossed Modules
-- 4.1 Strict 2-Groups
-- 4.2 Crossed Modules
-- 4.3 Group Actions and Split Monomorphisms
-- 4.4 Precrossed Modules and Internal Reflexive Graphs
-- 4.5 Crossed Modules and Peiffer Graphs
-- 4.6 Peiffer Graphs and Strict 2-Groups
----------------------------------------------------------------------------

-- 4.1 Strict 2-Groups
-- 4.2 Crossed Modules
-- 4.3 Group Actions and Split Monomorphisms
-- 4.4 Precrossed Modules and Internal Reflexive Graphs
-- 4.5 Crossed Modules and Peiffer Graphs
-- 4.6 Peiffer Graphs and Strict 2-Groups

--------------------------------------------------------
-- 5.  Higher Groups in Cubical Type Theory
-- 5.1 Pointed Types
-- 5.2 Homotopy Groups
-- 5.3 Higher Groups
-- 5.4 Eilenberg-MacLane-Spaces
-- 5.5 Delooping Groups
-------------------------------------------------------

-- 5.1 Pointed Types
-- 5.2 Homotopy Groups
-- 5.3 Higher Groups
-- 5.4 Eilenberg-MacLane-Spaces
-- 5.5 Delooping Groups

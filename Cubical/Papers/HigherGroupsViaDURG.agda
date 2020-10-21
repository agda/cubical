{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Papers.HigherGroupsViaDURG where

-- Johannes Schipp von Branitz,
-- "Higher Groups via Displayed Univalent Reflexive Graphs in Cubical Type Theory".

import Cubical.Algebra.Group as Group

import Cubical.Core.Glue as Glue

import Cubical.Data.Sigma.Properties as Sigma
import Cubical.Data.Unit as Unit

import Cubical.DStructures.Base as DSBase

import Cubical.DStructures.Meta.Properties as DSProperties
import Cubical.DStructures.Meta.Isomorphism as DSIsomorphism

import Cubical.DStructures.Structures.Action as DSAction
import Cubical.DStructures.Structures.Category as DSCategory
import Cubical.DStructures.Structures.Constant as DSConstant
import Cubical.DStructures.Structures.Group as DSGroup
import Cubical.DStructures.Structures.Higher as DSHigher
import Cubical.DStructures.Structures.Nat as DSNat
import Cubical.DStructures.Structures.PeifferGraph as DSPeifferGraph
import Cubical.DStructures.Structures.ReflGraph as DSReflGraph
import Cubical.DStructures.Structures.SplitEpi as DSSplitEpi
import Cubical.DStructures.Structures.Strict2Group as DSStrict2Group
import Cubical.DStructures.Structures.Type as DSType
import Cubical.DStructures.Structures.Universe as DSUniverse
import Cubical.DStructures.Structures.VertComp as DSVertComp
import Cubical.DStructures.Structures.XModule as DSXModule
import Cubical.DStructures.Equivalences.GroupSplitEpiAction as DSGroupSplitEpiAction
import Cubical.DStructures.Equivalences.PreXModReflGraph as DSPreXModReflGraph
import Cubical.DStructures.Equivalences.XModPeifferGraph as DSXModPeifferGraph
import Cubical.DStructures.Equivalences.PeifferGraphS2G as DSPeifferGraphS2G

import Cubical.Foundations.GroupoidLaws as GroupoidLaws
import Cubical.Foundations.Equiv as Equiv
import Cubical.Foundations.Equiv.Fiberwise as Fiberwise
import Cubical.Foundations.Filler as Filler
import Cubical.Foundations.HLevels as HLevels
import Cubical.Foundations.HLevels' as HLevels'
import Cubical.Foundations.Isomorphism as Isomorphism
import Cubical.Foundations.Prelude as Prelude
import Cubical.Foundations.Path as FPath
import Cubical.Foundations.Pointed as Pointed
import Cubical.Foundations.Univalence as Univalence
import Cubical.Foundations.Transport as Transport

import Cubical.Functions.FunExtEquiv as FunExtEquiv
import Cubical.Functions.Fibration as Fibration

import Cubical.Relation.Binary as Binary

import Cubical.HITs.EilenbergMacLane1 as EM1

import Cubical.Homotopy.Base as HomotopyBase
import Cubical.Homotopy.Connected as Connected
import Cubical.Homotopy.PointedFibration as PointedFibration
import Cubical.Homotopy.Loopspace as Loopspace

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
open Fiberwise using (fiberEquiv;
                     totalEquiv) public

-- Proposition 2.11
open Sigma using (Σ-cong-equiv) public

-- Definition 2.12
open HomotopyBase using (_∼_) public

-- Theorem 2.13
open FunExtEquiv using (funExtEquiv) public

-- Theorem 2.14
open Univalence using (univalence) public
                renaming (ua to idToEquiv⁻¹;
                          uaβ to idToEquiv-β;
                          uaη to idToEquiv-η) public

-- Lemma 2.15
open Univalence using (ua→) public


-- 2.5 Truncated and Connected Types


open Prelude using (isProp;
                   isSet) public
open HLevels using (isOfHLevel;
                   TypeOfHLevel) public

-- Lemma 2.16
open Sigma using (Σ-contractFst;
                 Σ-contractSnd) public

-- Lemma 2.17
open Prelude using (isProp→PathP) public

-- Lemma 2.18
open Subtype using (subtypeWitnessIrrelevance) public
open Sigma using (Σ≡Prop) public

-- Definition 2.19
open HLevels using (isOfHLevelDep) public

-- Proposition 2.20
open HLevels' using (truncSelfId→truncId) public

-- Proposition 2.21
open HLevels using (isOfHLevelΣ) public

-- Proposition 2.22
open HLevels using (isPropIsOfHLevel) public

-- Proposition 2.23
open HLevels using (isOfHLevelΠ) public

-- Theorem 2.24
open Truncation using (∥_∥_;
                      rec;
                      elim) public

-- Definition 2.25
open Connected using (isConnected;
                     isConnectedFun) public

-- Lemma 2.26
open Connected using (isConnectedPoint) public


-- 2.6 Groups

-- Proposition 2.28
open Group using (isPropIsGroupHom;
                 isSetGroupHom) public

-- Proposition 2.29
open Group.Kernel using (ker) public

-- Proposition 2.30
open Group using (GroupMorphismExt) public

-- Theorem 2.31
open Group using (GroupPath) public

-- Definition 2.32
open Group using (isGroupSplitEpi) public

-- Definition 2.33
open Group using (GroupAction;
                 IsGroupAction) public

-- Proposition 2.34
open Group using (semidirectProd) public


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

-- Proposition 3.1
open Fibration using (dispTypeIso) public

-- 3.2 Displayed Categories

-- Definition 3.2
-- not implemented

-- Theorem 3.3
-- not implemented

-- 3.3 Univalent Reflexive Graphs

-- Definition 3.4, 3.5
open DSBase using (URGStr) public

-- Example 3.6
open DSGroup using (𝒮-group) public

-- Example 3.7
open DSCategory using (Cat→𝒮) public

-- Proposition 3.8
-- not implemented

-- Example 3.9
open DSNat using (𝒮-Nat) public

-- Theorem 3.10
open Binary using (contrRelSingl→isUnivalent;
                  isUnivalent→contrRelSingl) public

-- Example 3.11
open DSType using (𝒮-type) public
open DSUniverse using (𝒮-universe) public

-- Proposition 3.12
open DSType using (𝒮-uniqueness) public


-- 3.4 Displayed Univalent Reflexive Graphs


-- Proposition 3.13
open DSBase using (URGStrᴰ) public

open DSBase using (make-𝒮ᴰ) public

-- Proposition 3.14
open DSType using (Subtype→Sub-𝒮ᴰ) public

-- Example 3.15
open DSHigher using (𝒮ᴰ-connected;
                    𝒮ᴰ-truncated) public


-- 3.5 Operations on Displayed Univalent Reflexive Graphs


-- Theorem 3.16
open DSProperties using (∫⟨_⟩_) public

-- Corollary 3.17
open DSConstant using (𝒮ᴰ-const) public

-- Definition 3.18
open DSConstant using (_×𝒮_) public

-- Theorem 3.19
open DSProperties using (splitTotal-𝒮ᴰ) public

-- Proposition 3.20
open DSProperties using (VerticalLift-𝒮ᴰ) public

-- Corollary 3.21
open DSProperties using (combine-𝒮ᴰ) public


-- 3.6 Constructing Equivalences Using Displayed Univalent Reflexive Graphs


-- Definition 3.22
open Binary using (RelIso) public

-- Proposition 3.23
open DSIsomorphism using (𝒮-PIso;
                         𝒮-PIso→Iso) public

-- Definition 3.24, Theorem 3.25
open Binary using (RelFiberIsoOver→Iso) public
open DSIsomorphism using (𝒮ᴰ-♭PIso-Over→TotalIso) public

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


-- Example 4.1
-- not implemented


-- 4.2 Crossed Modules


-- Definition 4.2, Example 4.3
-- not implemented


-- 4.3 Group Actions and Split Monomorphisms


-- Proposition 4.4
open DSGroup using (𝒮ᴰ-G²\F;
                   𝒮ᴰ-G²\B;
                   𝒮ᴰ-G²\FB) public

-- Lemma 4.5
open DSSplitEpi using (𝒮ᴰ-SplitEpi) public

-- Lemma 4.6
open DSAction using (𝒮ᴰ-G²\Las) public

-- Lemma 4.7
open DSAction using (𝒮ᴰ-G²Las\Action) public


-- Proposition 4.8, Proposition 4.9, Lemma 4.10, Theorem 4.11
open DSGroupSplitEpiAction using (𝒮ᴰ-Iso-GroupAct-SplitEpi-*;
                                 IsoActionSplitEpi) public


-- 4.4 Precrossed Modules and Internal Reflexive Graphs


-- Lemma 4.12
open DSXModule using (𝒮ᴰ-Action\PreXModuleStr) public

-- Definition 4.13
open DSXModule using (isEquivariant;
                     isPropIsEquivariant;
                     PreXModule) public

-- Lemma 4.14
open DSSplitEpi using (𝒮ᴰ-G²FBSplit\B) public

-- Lemma 4.15
open DSReflGraph using (𝒮ᴰ-ReflGraph; ReflGraph) public

-- Lemma 4.16, Lemma 4.17, Lemma 4.18, Theorem 4.19
open DSPreXModReflGraph using (𝒮ᴰ-♭PIso-PreXModule'-ReflGraph';
                              Iso-PreXModule-ReflGraph) public


-- 4.5 Crossed Modules and Peiffer Graphs

-- Definition 4.20
open DSXModule using (XModule;
                     isPeiffer;
                     isPropIsPeiffer) public

-- Definition 4.21
open DSPeifferGraph using (isPeifferGraph;
                          isPropIsPeifferGraph) public

-- Lemma 4.22, Lemma 4.2.3, Theorem 4.24
open DSXModPeifferGraph public


-- 4.6 Peiffer Graphs and Strict 2-Groups


-- Definition 4.25
open DSVertComp using (VertComp) public

-- Proposition 4.26
open DSVertComp using (VertComp→+₁) public

-- Proposition 4.27
open DSVertComp using (isPropVertComp) public

-- Proposition 4.28, Proposition 4.29, Theorem 4.30
open DSPeifferGraphS2G public




--------------------------------------------------------
-- 5.  Higher Groups in Cubical Type Theory
-- 5.1 Pointed Types
-- 5.2 Homotopy Groups
-- 5.3 Higher Groups
-- 5.4 Eilenberg-MacLane-Spaces
-- 5.5 Delooping Groups
-------------------------------------------------------


-- 5.1 Pointed Types


-- Proposition 5.1
open DSUniverse using (𝒮ᴰ-pointed) public

-- Definition 5.2
open Pointed using (Π∙) public

-- Definition 5.3
open Pointed using (_∙∼_;
                   _∙∼P_) public

-- Proposition 5.4
open Pointed using (∙∼≃∙∼P) public

-- Theorem 5.5
open Pointed using (funExt∙≃) public

-- Theorem 5.6
open PointedFibration using (sec∙Trunc') public


-- 5.2 Homotopy Groups


-- Definition 5.7
open Loopspace using (Ω) public

-- Definition 5.8
open Group using (π₁-1BGroup) public


-- 5.3 Higher Groups


-- Lemma 5.9
open DSHigher using (𝒮-BGroup) public

-- Definition 5.10
open Group using (BGroup) public

-- Proposition 5.11
open DSHigher using (𝒮ᴰ-BGroupHom) public

-- Corollary 5.12
-- not implemented


-- 5.4 Eilenberg-MacLane-Spaces


-- Definition 5.13
open EM1 using (EM₁) public

-- Lemma 5.14
open EM1 using (emloop-comp) public

-- Lemma 5.15
open EM1 using (elimEq) public

-- Theorem 5.16
open EM1 renaming (elim to EM₁-elim;
                  rec to EM₁-rec) public

-- Lemma 5.17
open Group using (emloop-id;
                 emloop-inv) public

-- Theorem 5.18
open Group using (π₁EM₁≃) public

-- 5.5 Delooping Groups

-- Proposition 5.19, Theorem 5.20
open DSHigher using (𝒮-Iso-BGroup-Group) public

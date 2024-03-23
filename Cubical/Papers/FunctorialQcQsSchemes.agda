{-

Please do not move this file. Changes should only be made if necessary.

This file contains pointers to the code examples and main results from
the paper:

The Functor of Points approach to Schemes in Cubical Agda

Max Zeuner, Matthias Hutzler

Preprint: TODO ArXiv link


-}

-- The "--safe" flag ensures that there are no postulates or unfinished goals
{-# OPTIONS --safe #-}
module Cubical.Papers.FunctorialQcQsSchemes where


-- 2: Background
-- 2.1: Univalent type theory in Cubical Agda
import Cubical.Foundations.Prelude                              as Prelude
import Cubical.Foundations.HLevels                              as HLevels
import Cubical.Foundations.Univalence                           as Univalence
import Cubical.Data.Sigma                                       as Sigma
import Cubical.HITs.PropositionalTruncation                     as PT
import Cubical.HITs.SetQuotients                                as SQ

-- 2.2: Localizations and the Zariski lattice
import Cubical.Algebra.CommRing.Localisation.InvertingElements  as LocalizationInvEl
module LocalizationInvElBase = LocalizationInvEl.InvertingElementsBase
module LocalizationInvElUniversalProp = LocalizationInvElBase.UniversalProp

import Cubical.Algebra.ZariskiLattice.Base                      as ZLB
module ZariskiLatDef = ZLB.ZarLat

import Cubical.Algebra.ZariskiLattice.UniversalProperty         as ZLUP
module ZariskiLatUnivProp = ZLUP.ZarLatUniversalProp

module Localization&Radicals = LocalizationInvEl.RadicalLemma
import Cubical.Algebra.ZariskiLattice.Properties                as ZLP

-- 3: ℤ-functors
import Cubical.Categories.Instances.ZFunctors                   as ZFun
module RelativeAdjunction = ZFun.AdjBij

-- 4: Local ℤ-functors
import Cubical.Categories.Site.Cover                            as Cover
import Cubical.Categories.Site.Coverage                         as Coverage
import Cubical.Categories.Site.Sheaf                            as Sheaf

import Cubical.Categories.Site.Instances.ZariskiCommRing        as ZariskiCoverage
module ZarCovSubcanonical = ZariskiCoverage.SubcanonicalLemmas
import Cubical.Algebra.CommRing.Localisation.Limit              as LocalizationLimit

-- !!! note: the ZFunctors file is supposed to be broken up into smaller files !!!
-- 5: Compact opens and qcqs-schemes
-- import Cubical.Categories.Instances.ZFunctors                as ZFun

-- 6: Open subschemes
-- import Cubical.Categories.Instances.ZFunctors                as ZFun
module StandardOpen = ZFun.StandardOpens





---------- 2: Background  ----------
---------- 2.2: Univalent type theory Cubical Agda ----------

-- path type in Cubical Agda
open Prelude using (_≡_)

-- the first two h-levels
open Prelude using (isProp ; isSet)
open HLevels using (hProp)

-- univalence and the cubical SIP
open Univalence using (ua)
import Cubical.Foundations.SIP

-- set-quotients
open SQ using (_/_)

-- propositional truncation
open PT renaming (∥_∥₁ to ∥_∥)

-- ∃ notation in Cubical Agda
open Sigma using (∃-syntax)



---------- 2.2: Localizations and the Zariski lattice ----------

-- localization away from element
open LocalizationInvElBase using (R[1/_] ; R[1/_]AsCommRing)
open LocalizationInvElUniversalProp using (_/1 ; invElemUniversalProp)

-- Zariski lattice
open ZariskiLatDef using (ZariskiLattice ; _∼≡_)

-- supports
open ZLUP.IsSupport

-- support map D and universal property
open ZariskiLatUnivProp using (D ; isSupportD)
open ZariskiLatUnivProp using (ZLHasUniversalProp ; ⋁D≡)

-- facts about Zariski lattice and localization
open Localization&Radicals using (toUnit)
open ZLP using (unitLemmaZarLat)



----------- 3: ℤ-functors ----------

-- Definition 1
open ZFun using (ℤFunctor ; Sp ; 𝔸¹ ; isAffine)

-- Definition 3
open ZFun using (𝓞)

-- Proposition 4
open RelativeAdjunction
     using (𝓞⊣SpIso ; 𝓞⊣SpNatℤFunctor ; 𝓞⊣SpNatCommRing ; 𝓞⊣SpCounitEquiv)



---------- 4: Local ℤ-functors ----------

-- Definition 6
open Cover using (Cover)
open Coverage using (Coverage)

-- Definition 7
open Sheaf using (isCompatibleFamily ; CompatibleFamily)

-- the induced map σ
open Sheaf renaming (elementToCompatibleFamily to σ)

-- Definition 8
open Sheaf using (isSheaf ; hasAmalgamationPropertyForCover)

-- Definition 9
open Sheaf using (isSubcanonical)

-- Definition 10 & Lemma 11
open ZariskiCoverage using (UniModVec ; pullbackUniModVec ; zariskiCoverage)
open ZFun using (isLocal)

--Theorem 12
open LocalizationLimit using (equalizerLemma)
open ZarCovSubcanonical using (applyEqualizerLemma)
open ZariskiCoverage using (isSubcanonicalZariskiCoverage)



---------- 4: Compact opens and qcqs-schemes ----------

-- Definition 13
open ZFun renaming (ZarLatFun to 𝓛)

-- Definition 14
open ZFun using (CompactOpen ; ⟦_⟧ᶜᵒ)

-- Definition 15
open ZFun using (CompOpenDistLattice)

-- Definition 16
open ZFun using (isQcQsScheme)

-- Proposition 17
open ZFun using (singlAffineCover ; isQcQsSchemeAffine)

-- Remark 18
open ZFun using (AffineCover ; hasAffineCover)



----------- 5: Open subschemes ----------

-- Lemma 20
open ZFun using (isSeparatedZarLatFun)

-- Lemma 21
open ZFun using (presLocalCompactOpen)

-- Definition 22
open StandardOpen using (D)

-- Proposition 23
open StandardOpen using (SpR[1/f]≅⟦Df⟧ ; isAffineD)

-- Theorem 24
open ZFun using (isQcQsSchemeCompOpenOfAffine)

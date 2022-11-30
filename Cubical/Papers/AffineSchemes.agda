{-

Please do not move this file. Changes should only be made if necessary.

This file contains pointers to the code examples and main results from
the paper:

A Univalent Formalization of Affine Schemes

Anders Mörtberg, Max Zeuner

Preprint: !!! arXiv link !!!


-}

-- The "--safe" flag ensures that there are no postulates or unfinished goals
{-# OPTIONS --safe #-}
module Cubical.Papers.AffineSchemes where

-- 1: Introduction
-- should be no code


-- 2: Background
-- 2.2: Cubical Agda


-- 3: Commutative Algebra
-- 3.1: Localization
import Cubical.HITs.SetQuotients                                as SetQuotients
import Cubical.Algebra.CommRing.Localisation.Base               as L
module Localization = L.Loc

import Cubical.Algebra.CommRing.Localisation.UniversalProperty  as LocalizationUnivProp

import Cubical.Algebra.CommRing.Localisation.InvertingElements  as LocalizationInvEl
import Cubical.Algebra.CommAlgebra                              as R-Algs
import Cubical.Algebra.CommAlgebra.Localisation                 as LocalizationR-Alg

-- 3.2: The Zariski Lattice
import Cubical.Data.FinData.Base                                as FiniteTypes
import Cubical.Algebra.Matrix                                   as Matrices
import Cubical.Algebra.CommRing.FGIdeal                         as FinGenIdeals

import Cubical.Algebra.ZariskiLattice.Base                      as ZLB
module ZariskiLatDef = ZLB.ZarLat

import Cubical.Algebra.ZariskiLattice.UniversalProperty         as ZLUP
module ZariskiLatUnivProp = ZLUP.ZarLatUniversalProp


-- 4: Category Theory
-- background theory not explicitly mentioned
import Cubical.Categories.Category.Base                         as CatTheory
import Cubical.Categories.Limits                                as GeneralLimits
import Cubical.Categories.Limits.RightKan                       as GeneralKanExtension

import Cubical.Categories.DistLatticeSheaf.Diagram              as SheafDiagShapes
import Cubical.Categories.DistLatticeSheaf.Base                 as Sheaves

import Cubical.Categories.DistLatticeSheaf.Extension            as E
module SheafExtension = E.PreSheafExtension

-- 5: The Structure Sheaf
import Cubical.Algebra.CommAlgebra.Properties                   as R-AlgProps
import Cubical.Categories.Instances.CommAlgebras                as R-AlgConstructions
import Cubical.Algebra.CommRing.Localisation.Limit              as LocalizationLimit
import Cubical.Algebra.ZariskiLattice.StructureSheaf            as StructureSheaf



---------- 2: Background  ----------
---------- 2.2: A brief introduction to Cubical Agda ----------



---------- 3: Commutative Algebra  ----------
---------- 3.1: Localization ----------

-- definition of localization
open Localization using (_≈_ ; S⁻¹R ; S⁻¹RAsCommRing)

-- Remark
open SetQuotients using (truncRelEquiv)

-- canonical homomorphism
open LocalizationUnivProp.S⁻¹RUniversalProp using (_/1)

-- universal property
open LocalizationUnivProp.S⁻¹RUniversalProp using (S⁻¹RHasUniversalProp)

-- Lemma
open LocalizationUnivProp using (S⁻¹RChar)

-- localization away from element
open LocalizationInvEl.InvertingElementsBase using ([_ⁿ|n≥0] ; R[1/_] ; R[1/_]AsCommRing)

-- Lemma
-- 1.
open LocalizationInvEl.DoubleLoc using (R[1/fg]≡R[1/f][1/g])
-- 2.
open LocalizationInvEl using (invertingUnitsPath)
-- 3. is actually proved more generally for R-algebras, see below

-- R-algebras as pairs
open R-Algs.CommAlgChar

-- universal property for localizations as R-algebras
open LocalizationR-Alg.AlgLoc using (S⁻¹RHasAlgUniversalProp)

-- R-algebra version of lemma
open LocalizationR-Alg.AlgLoc using (S⁻¹RAlgCharEquiv)

-- R-algebra version of lemma
-- 1.
open LocalizationR-Alg.DoubleAlgLoc using (R[1/fg]≡R[1/f][1/g])
-- 3.
open LocalizationR-Alg.AlgLocTwoSubsets using (isContrS₁⁻¹R≡S₂⁻¹R)



---------- 3.2: Zariski Lattice ----------

-- the two equivalence relations and their equivalence
open ZariskiLatDef renaming (_∼≡_ to _≋_) using (_∼_)
open ZariskiLatDef using (≡→∼ ; ∼→≡)

-- defintion of Zariski lattice
open ZariskiLatDef using (ZL)

-- _++_ and relation to ideal addition
open FiniteTypes renaming (_++Fin_ to _++_)
open FinGenIdeals using (FGIdealAddLemma)

-- _··_ and relation to ideal multiplication
open Matrices.ProdFin renaming (_··Fin_ to _··_)
open FinGenIdeals using (FGIdealMultLemma)

-- lattice structure and laws
open ZariskiLatDef using (ZariskiLattice)

-- support map D and universal property
open ZariskiLatUnivProp using (D ; isZarMapD)
open ZariskiLatUnivProp using (ZLHasUniversalProp)

-- D(g) ≤ D(f) ⇔ isContr (R-Hom R[1/f] R[1/g])
open StructureSheaf using (contrHoms)

-- basic opens
open StructureSheaf using (BasicOpens ; BO)

-- basic opens form basis
open ZariskiLatUnivProp using (ZLUniversalPropCorollary ; ⋁D≡)
open StructureSheaf using (basicOpensAreBasis)



---------- 4: Category Theory  ----------

-- Σ-subcategories
open CatTheory using (ΣPropCat)

-- Kan-extension for distributive lattices
open SheafExtension using (DLRan ; DLRanNatIso)

-- Definition
open SheafDiagShapes using (DLShfDiagOb ; DLShfDiagHom ; DLShfDiag)

-- Remark
open SheafDiagShapes.DLShfDiagHomPath using (isSetDLShfDiagHom)

-- diagram associated to a vector
open SheafDiagShapes using (FinVec→Diag)

-- Definition
open Sheaves using (isDLSheaf)
open Sheaves.SheafOnBasis using (isDLBasisSheaf)

-- Lemma
open Sheaves using (isDLSheafPullback)
open Sheaves.EquivalenceOfDefs using (L→P ; P→L)

-- Lemma
open SheafExtension using (coverLemma)

-- Theorem
open SheafExtension using (isDLSheafDLRan)



---------- 5: The Structure Sheaf ----------

-- Lemma
open R-AlgProps using (recPT→CommAlgebra)

-- Lemma
open R-AlgConstructions.PreSheafFromUniversalProp renaming (universalPShf to 𝓟ᵤ)

-- definition of structure sheaf
open StructureSheaf using ( 𝓞ᴮ ; 𝓞 )

-- Proposition
open StructureSheaf using (baseSections)

-- Corollary
open StructureSheaf using (globalSection)

-- Lemma
open LocalizationLimit using (isLimConeLocCone)

-- Theorem
open StructureSheaf using (isSheaf𝓞ᴮ)

-- Corollary
open StructureSheaf using (isSheaf𝓞)

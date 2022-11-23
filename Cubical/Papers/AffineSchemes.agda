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
import Cubical.Algebra.CommRing.Localisation.Base               as Localization
import Cubical.Algebra.CommRing.Localisation.UniversalProperty  as LocalizationUnivProp
import Cubical.Algebra.CommRing.Localisation.InvertingElements  as LocalizationInvEl
import Cubical.Algebra.CommAlgebra.Localisation                 as LocalizationRAlg

-- 3.2: The Zariski Lattice
import Cubical.Algebra.ZariskiLattice.Base                      as ZariskiLatDef
import Cubical.Algebra.ZariskiLattice.UniversalProperty         as ZariskiLatUnivProp


-- 4: Category Theory
-- background theory not explicitly mentioned
import Cubical.Categories.Category.Base                         as CatTheory
import Cubical.Categories.Limits                                as GeneralLimits
import Cubical.Categories.Limits.RightKan                       as GeneralKanExtension

import Cubical.Categories.DistLatticeSheaf.Diagram              as SheafDiagShapes
import Cubical.Categories.DistLatticeSheaf.Base                 as Sheaves
import Cubical.Categories.DistLatticeSheaf.Extension            as SheafExtension

-- 5: The Structure Sheaf
import Cubical.Algebra.CommAlgebra.Properties                   as RAlgProps
import Cubical.Categories.Instances.CommAlgebras                as RAlgConstructions
import Cubical.Algebra.CommRing.Localisation.Limit              as LocalizationLimit
import Cubical.Algebra.ZariskiLattice.StructureSheaf            as StructureSheaf



---------- 2: Background  ----------
---------- 3: Commutative Algebra  ----------
---------- 4: Category Theory  ----------

-- Σ-subcategories
open CatTheory using (ΣPropCat)

-- Kan-extension for distributive lattices
open SheafExtension.PreSheafExtension using (DLRan ; DLRanNatIso)

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

-- Theorem
open SheafExtension.PreSheafExtension using (isDLSheafDLRan)


---------- 5: The Structure Sheaf ----------

-- Lemma
open RAlgProps using (recPT→CommAlgebra)

-- Lemma
open RAlgConstructions.PreSheafFromUniversalProp using (universalPShf)

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

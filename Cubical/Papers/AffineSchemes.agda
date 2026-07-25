{-

Please do not move this file. Changes should only be made if necessary.

This file contains pointers to the code examples and main results from
the paper:

A Univalent Formalization of Constructive Affine Schemes

Max Zeuner, Anders Mörtberg

Available at: https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.TYPES.2022.14

ArXiv version: https://arxiv.org/abs/2212.02902


-}

-- The "--safe" flag ensures that there are no postulates or unfinished goals
module Cubical.Papers.AffineSchemes where



-- 2: Background
-- 2.2: Cubical Agda
import Cubical.Foundations.Prelude                                 as Prelude
import Cubical.Foundations.HLevels                                 as HLevels
import Cubical.Foundations.Univalence                              as Univalence
import Cubical.Data.Sigma                                          as Sigma
import Cubical.HITs.PropositionalTruncation                        as PT
import Cubical.Algebra.DistLattice.Basis                           as DistLatticeBasis
import Cubical.HITs.SetQuotients                                   as SQ


-- 3: Commutative Algebra
-- 3.1: Localization
import Cubical.Algebra.CommRing.Localisation.Base                  as L
module Localization = L.Loc

import Cubical.Algebra.CommRing.Localisation.UniversalProperty     as LocalizationUnivProp
import Cubical.Algebra.CommRing.Localisation.InvertingElements     as LocalizationInvEl
import Cubical.Algebra.CommAlgebra.AsModule                     as R-Algs
import Cubical.Algebra.CommAlgebra.AsModule.Localisation        as LocalizationR-Alg


-- 3.2: The Zariski Lattice
import Cubical.Data.FinData.Base                                   as FiniteTypes
import Cubical.Algebra.Matrix                                      as Matrices
import Cubical.Algebra.CommRing.FGIdeal                            as FinGenIdeals

import Cubical.AlgebraicGeometry.ZariskiLattice.Base               as ZLB
module ZariskiLatDef = ZLB.ZarLat

import Cubical.AlgebraicGeometry.ZariskiLattice.UniversalProperty  as ZLUP
module ZariskiLatUnivProp = ZLUP.ZarLatUniversalProp


-- 4: Category Theory
-- background theory not explicitly mentioned
import Cubical.Categories.Instances.FullSubcategory                as CatTheory
import Cubical.Categories.Limits                                   as GeneralLimits
import Cubical.Categories.Limits.RightKan                          as GeneralKanExtension

import Cubical.Categories.DistLatticeSheaf.Diagram                 as SheafDiagShapes
import Cubical.Categories.DistLatticeSheaf.Base                    as Sheaves

import Cubical.Categories.DistLatticeSheaf.Extension               as E
module SheafExtension = E.PreSheafExtension


-- 5: The Structure Sheaf
import Cubical.Categories.Instances.CommAlgebras                   as R-AlgConstructions
import Cubical.Algebra.CommRing.Localisation.Limit                 as LocalizationLimit
import Cubical.AlgebraicGeometry.ZariskiLattice.StructureSheaf     as StructureSheaf




---------- 2: Background  ----------
---------- 2.2: A brief introduction to Cubical Agda ----------

-- path type in Cubical Agda
open Prelude using (_≡_ ; PathP)

-- univalence and the cubical SIP
open Univalence using (ua)
import Cubical.Foundations.SIP
open R-Algs renaming (uaCommAlgebra to sip)

-- the first three h-levels
open Prelude using (isContr ; isProp ; isSet)
open HLevels using (hProp)

-- propositional truncation; In the agda/cubical library the indexing of
-- truncations is shifted by +2 and start at 0 instead of -2, hence
-- propositional truncation is ∥_∥₁.
open PT renaming (∥_∥₁ to ∥_∥)

-- ∃ notation in Cubical Agda
open Sigma using (∃-syntax)

-- example of a basis of a distributive lattice
open DistLatticeBasis using (IsBasis)

-- Set quotients
open SQ using (_/_)



---------- 3: Commutative Algebra  ----------
---------- 3.1: Localization ----------

-- definition of localization
open Localization using (_≈_ ; S⁻¹R ; S⁻¹RAsCommRing)

-- Remark 1
open SQ using (truncRelEquiv)

-- canonical homomorphism
open LocalizationUnivProp.S⁻¹RUniversalProp using (_/1)

-- universal property
open LocalizationUnivProp.S⁻¹RUniversalProp using (S⁻¹RHasUniversalProp)

-- R-algebras as pairs
open R-Algs.CommAlgChar

-- universal property for localizations as R-algebras
open LocalizationR-Alg.AlgLoc using (S⁻¹RHasAlgUniversalProp)

-- Lemma 2
open LocalizationUnivProp using (S⁻¹RChar)
open LocalizationR-Alg.AlgLoc using (S⁻¹RAlgCharEquiv)

-- localization away from element
open LocalizationInvEl.InvertingElementsBase using ([_ⁿ|n≥0] ; R[1/_] ; R[1/_]AsCommRing)

-- Lemma 3
-- 1.
open LocalizationInvEl.DoubleLoc using (R[1/fg]≡R[1/f][1/g])
open LocalizationR-Alg.DoubleAlgLoc using (R[1/fg]≡R[1/f][1/g])
-- 2.
open LocalizationInvEl using (invertingUnitsPath)
-- 3.
open LocalizationR-Alg.AlgLocTwoSubsets using (isContrS₁⁻¹R≡S₂⁻¹R)



---------- 3.2: Zariski Lattice ----------

-- Zariski lattice as set-quotient and
-- equivalence of quotienting relations
open ZariskiLatDef using (_∼_ ; ZL) renaming (_∼≡_ to _≋_)
open ZariskiLatDef using (≡→∼ ; ∼→≡)

-- _++_ and relation to ideal addition
open FiniteTypes renaming (_++Fin_ to _++_)
open FinGenIdeals using (FGIdealAddLemma)

-- _··_ and relation to ideal multiplication
open Matrices.ProdFin renaming (_··Fin_ to _··_)
open FinGenIdeals using (FGIdealMultLemma)

-- lattice structure and laws
open ZariskiLatDef using (ZariskiLattice)

-- support map D and universal property
open ZariskiLatUnivProp using (D ; isSupportD)
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

-- Definition 4
open SheafDiagShapes using (DLShfDiagOb ; DLShfDiagHom ; DLShfDiag)

-- Remark 5
open SheafDiagShapes.DLShfDiagHomPath using (isSetDLShfDiagHom)

-- diagram associated to a vector
open SheafDiagShapes using (FinVec→Diag)

-- Definition 6
open Sheaves using (isDLSheaf)

-- Definition 7
open Sheaves.SheafOnBasis using (isDLBasisSheaf)

-- Lemma 8
open Sheaves using (isDLSheafPullback)
open Sheaves.EquivalenceOfDefs using (L→P ; P→L)

-- Lemma 9
open SheafExtension using (coverLemma)

-- Theorem 10
open SheafExtension using (isDLSheafDLRan)



---------- 5: The Structure Sheaf ----------

-- Lemma 11
open R-Algs using (recPT→CommAlgebra)

-- Lemma 12
open R-AlgConstructions.PreSheafFromUniversalProp renaming (universalPShf to 𝓟ᵤ)

-- definition of structure sheaf
open StructureSheaf using ( 𝓞ᴮ ; 𝓞 )

-- Proposition 13
open StructureSheaf using (baseSections)

-- Corollary 14
open StructureSheaf using (globalSection)

-- Lemma 15
open LocalizationLimit using (isLimConeLocCone)

-- Theorem 16
open StructureSheaf using (isSheaf𝓞ᴮ)

-- Corollary 17
open StructureSheaf using (isSheaf𝓞)

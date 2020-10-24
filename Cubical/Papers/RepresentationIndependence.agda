{-
Please do not move this file. Changes should only be made if necessary.

This file contains pointers to the code examples and main results from the paper:

Internalizing Representation Independence with Univalence

Carlo Angiuli, Evan Cavallo, Anders Mörtberg, Max Zeuner

Preprint: https://arxiv.org/abs/2009.05547

-}
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Papers.RepresentationIndependence where


-- 2.1
import Agda.Builtin.Cubical.Path               as Path
import Cubical.Foundations.Prelude             as Prelude
-- 2.2
import Cubical.Foundations.Univalence          as Univalence
import Cubical.Foundations.HLevels             as HLevels
import Cubical.Foundations.Equiv               as Equivalences
import Cubical.Data.Sigma.Properties           as Sigma
-- 2.3
import Cubical.HITs.PropositionalTruncation    as PropositionalTruncation
import Cubical.HITs.Cost.Base                  as CostMonad
import Cubical.HITs.SetQuotients               as SetQuotients
import Cubical.HITs.Rationals.QuoQ             as SetQuoQ
import Cubical.HITs.Rationals.SigmaQ           as SigmaQ
-- 3.1
import Cubical.Foundations.SIP                 as SIP
import Cubical.Structures.Axioms               as Axioms
import Cubical.Algebra.Monoid.Base             as Monoid
open import Cubical.Data.Sigma.Base
-- 3.2
import Cubical.Structures.Pointed              as PointedStr
import Cubical.Structures.Constant             as ConstantStr
import Cubical.Structures.Product              as ProductStr
import Cubical.Structures.Function             as FunctionStr
import Cubical.Structures.Maybe                as MaybeStr
import Cubical.Foundations.Structure           as Structure
import Cubical.Structures.Auto                 as Auto
open import Cubical.Data.Maybe.Base
-- 4.1
import Cubical.Data.Vec.Base                   as Vector
import Cubical.Algebra.Matrix                  as Matrices
import Cubical.Data.FinData.Base               as Finite
open import Cubical.Algebra.AbGroup.Base
open import Cubical.Data.Bool.Base
-- 4.2
import Cubical.Structures.Queue                as Queues
import Cubical.Data.Queue.Truncated2List       as BatchedQueues
-- 5.1
import Cubical.Relation.Binary.Base            as BinRel
import Cubical.Relation.ZigZag.Base            as QER
import Cubical.Relation.ZigZag.Applications.MultiSet
                                               as MultiSets
-- 5.2
import Cubical.Foundations.RelationalStructure as RelStructure
import Cubical.Structures.Relational.Function  as RelFunction



-------------------------------------------------------------------------
-- 2. Programming in Cubical Type Theory
-- 2.1 Equalities as Paths
-- 2.2 Univalence
-- 2.3 Higher Inductive Types
-------------------------------------------------------------------------


-- 2.1 Equalities as Paths
open Path using (PathP) public
open Prelude using (_≡_ ; refl ; cong ; funExt
                        ; transport ; subst ; J) public


-- 2.2 Univalence
open Univalence using (ua ; uaβ) public

-- Sets and Propositions
open Prelude using (isProp ; isSet) public
open HLevels using (isPropΠ) public
open Prelude using (isContr) public

-- Equivalences and Isomorphisms
open Equivalences using (isEquiv ; _≃_) public
open Equivalences renaming (fiber to preim) public
open Sigma using (ΣPath≃PathΣ) public
open Equivalences renaming (propBiimpl→Equiv to prop≃) public


-- 2.3 Higher Inductive Types
-- Propositional Truncation
open PropositionalTruncation using (∥_∥ ; map) public
open CostMonad using (Cost ; Cost≡ ; _>>=_ ; return
                           ; fib ; fibTail) public
-- Computation
_ : fib 20 ≡ (6765 , PropositionalTruncation.∣ 21890 ∣)
_ = refl

_ : fibTail 20 ≡ (6765 , PropositionalTruncation.∣ 19 ∣)
_ = refl

-- Set Quotients
open SetQuotients using (_/_ ; setQuotUniversal) public
-- Rational Numbers
open SetQuoQ using (_∼_ ; ℚ) public
open SigmaQ renaming (ℚ to ℚ') public



-------------------------------------------------------------------------
-- 3. The Structure Identity Principle
-- 3.1 Structures
-- 3.2 Building Strucutres
-------------------------------------------------------------------------

-- 3.1 Structures
open SIP using (TypeWithStr ; StrEquiv ; _≃[_]_
                            ; UnivalentStr ; SIP ; sip) public

-- the last two terms above correspond to lemma 3.3
-- and corollary 3.4 respectively
open Axioms using ( AxiomsStructure ; AxiomsEquivStr
                  ; axiomsUnivalentStr ; transferAxioms) public

-- Monoids are defined using records and Σ-types in the library
open Monoid.MonoidΣTheory using (RawMonoidStructure ; MonoidAxioms
                                                    ; MonoidStructure) public
open Monoid.MonoidΣTheory renaming (MonoidΣ to Monoid) public

MonoidEquiv : (M N : Monoid) → fst M ≃ fst N → Type
MonoidEquiv (_ , (εᴹ , _·_) , _) (_ , (εᴺ , _∗_) , _) (φ , _) =
  (φ εᴹ ≡ εᴺ) × (∀ x y → φ (x · y) ≡ (φ x) ∗ (φ y))


-- 3.2 Building Structures
-- Constant and Pointed Structures
open PointedStr using (PointedStructure ; PointedEquivStr
                                        ; pointedUnivalentStr) public
open ConstantStr using (ConstantStructure ; ConstantEquivStr
                                          ; constantUnivalentStr) public

-- Product Structures
open ProductStr using (ProductStructure ; ProductEquivStr
                                        ; productUnivalentStr) public

-- Function Structures
open FunctionStr using (FunctionEquivStr) public

-- Maybe Structures
open MaybeStr using (MaybeEquivStr) public

-- Transport Structures
open Structure using (EquivAction) public
open SIP using (TransportStr ; TransportStr→UnivalentStr
                             ; UnivalentStr→TransportStr) public
open Structure using (EquivAction→StrEquiv) public
open FunctionStr using (FunctionEquivStr+) public

-- Monoids Revisited
open Monoid.MonoidΣTheory using (MonoidΣPath ; InducedMonoid
                                             ; InducedMonoidPath) public

-- Automation
open Auto using (Transp[_] ; AutoEquivStr ; autoUnivalentStr) public
module _ (A : Type) (Aset : isSet A) where
 RawQueueEquivStr =
   AutoEquivStr (λ (X : Type) → X × (A → X → X) × (X → Transp[ Maybe (X × A) ]))



-------------------------------------------------------------------------
-- 4. Representation Independence through the SIP
-- 4.1 Matrices
-- 4.2 Queues
-------------------------------------------------------------------------


-- 4.1 Matrices
open Vector using (Vec) public
open Finite using (Fin ; _==_) public
open Matrices using (VecMatrix ; FinMatrix ; FinMatrix≡VecMatrix
                                           ; FinMatrix≃VecMatrix) public
open Matrices.FinMatrixAbGroup using (addFinMatrix ; addFinMatrixComm) public

-- example (not in the library)
open import Cubical.Data.Int renaming (Int to ℤ ; isSetInt to isSetℤ)

ℤ-AbGroup : AbGroup
ℤ-AbGroup = makeAbGroup {G = ℤ} 0 _+_ -_ isSetℤ +-assoc (λ x _ → x) rem +-comm
    where
    -_ : ℤ → ℤ
    - x = 0 - x
    rem : (x : ℤ) → x + (- x) ≡ 0
    rem x =  +-comm x (pos 0 - x) Prelude.∙ minusPlus x 0

module experiment where
  open Prelude

  M : FinMatrix ℤ 2 2
  M i j = if i == j then 1 else 0

  N : FinMatrix ℤ 2 2
  N i j = if i == j then 0 else 1

  replaceGoal : {A B : Type} {x y : A} → (e : A ≃ B)
                (h : invEq e (equivFun e x) ≡ invEq e (equivFun e y)) → x ≡ y
  replaceGoal e h = sym (secEq e _) ∙∙ h ∙∙ secEq e _

  _ : addFinMatrix ℤ-AbGroup M N ≡ (λ _ _ → 1)
  _ = replaceGoal (FinMatrix≃VecMatrix) refl


-- 4.2 Queues
open Queues.Queues-on using (RawQueueStructure ; QueueAxioms) public
open BatchedQueues.Truncated2List renaming (Q to BatchedQueueHIT)
                                  using (Raw-1≡2 ; WithLaws) public



-------------------------------------------------------------------------
-- 5. Structured Equivalences from Structured Relations
-- 5.1 Quasi-Equivalence Relations
-- 5.2 Structured Relations
-------------------------------------------------------------------------


-- 5.1 Quasi-Equivalence Relations
--Lemma (5.1)
open BinRel using (idPropRel ; invPropRel
                             ; compPropRel ; graphRel) public
-- Definitions (5.2) and (5.3)
open QER using (isZigZagComplete ; isQuasiEquivRel) public
-- Lemma (5.4)
open QER.QER→Equiv using (Thm ; bwd≡ToRel) public
-- Multisets
open MultiSets renaming (AList to AssocList) public
open MultiSets.Lists&ALists using (addIfEq ; R ; φ ; ψ
                                           ; List/Rᴸ≃AList/Rᴬᴸ) public
open MultiSets.Lists&ALists.L using (insert ; union ; count)
open MultiSets.Lists&ALists.AL using (insert ; union ; count)


-- 5.2 Structured Relations
open RelStructure using (StrRel) public
-- Definition (5.6)
open RelStructure using (SuitableStrRel) public
-- Theorem (5.7)
open RelStructure using (structuredQER→structuredEquiv) public
-- Definition (5.9)
open RelStructure using (StrRelAction) public
-- Lemma (5.10)
open RelStructure using (strRelQuotientComparison) public
-- Definition (5.11)
open RelStructure using (PositiveStrRel) public
-- Theorem (5.12)
open RelFunction using (functionSuitableRel) public
-- Multisets
-- (main is applying 5.7 to the example)
open MultiSets.Lists&ALists using (multisetShape ; isStructuredR ; main ; List/Rᴸ≡AList/Rᴬᴸ)
                            renaming ( hasAssociativeUnion to unionAssocAxiom
                                     ; LQassoc to LUnionAssoc
                                     ; ALQassoc to ALUnionAssoc) public

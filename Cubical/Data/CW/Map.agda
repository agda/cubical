{-# OPTIONS --cubical --safe --lossy-unification #-}

{-This file contains:

-}

module Cubical.Data.CW.Map where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Function

open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Unit
open import Cubical.Data.Fin
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sequence
open import Cubical.Data.FinSequence


open import Cubical.HITs.Sn
open import Cubical.HITs.Pushout
open import Cubical.HITs.Susp
open import Cubical.HITs.SequentialColimit
open import Cubical.HITs.SphereBouquet
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Data.CW.Base
open import Cubical.Data.CW.Properties


open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup

open import Cubical.HITs.SequentialColimit
open Sequence

open import Cubical.Relation.Nullary

private
  variable
    ℓ ℓ' ℓ'' : Level
    C D E : CWskel ℓ

-- Maps
cellMap : (C : CWskel ℓ) (D : CWskel ℓ') → Type (ℓ-max ℓ ℓ')
cellMap C D = SequenceMap (realiseSeq C) (realiseSeq D)

-- Extracting a map between the realisations of the CWskel complexes
realiseCellMap : cellMap C D → realise C → realise D
realiseCellMap mp C∞ = realiseSequenceMap mp C∞

-- The identity as a cellular map
idCellMap : (C : CWskel ℓ) → cellMap C C
idCellMap C = idSequenceMap _

-- Composition of two cellular maps
composeCellMap : (g : cellMap D E) (f : cellMap C D) → cellMap C E
composeCellMap = composeSequenceMap


----- finite versions of above -----
module _ (m : ℕ) where
  finCellMap : (C : CWskel ℓ) (D : CWskel ℓ') → Type (ℓ-max ℓ ℓ')
  finCellMap C D = FinSequenceMap (realiseFinSeq m C) (realiseFinSeq m D)

  idFinCellMap : (C : CWskel ℓ) → finCellMap C C
  idFinCellMap C = idFinSequenceMap m (realiseFinSeq m C)

  composeFinCellMap : (g : finCellMap D E) (f : finCellMap C D) → finCellMap C E
  composeFinCellMap = composeFinSequenceMap m

finCellMap↓ : {m : ℕ} {C : CWskel ℓ} {D : CWskel ℓ'}  → finCellMap (suc m) C D → finCellMap m C D
FinSequenceMap.fmap (finCellMap↓ {m = m} ϕ) x = FinSequenceMap.fmap ϕ (injectSuc x)
FinSequenceMap.fcomm (finCellMap↓ {m = m} {C = C}  ϕ) x r = FinSequenceMap.fcomm ϕ (injectSuc x) r
  ∙  λ t → FinSequenceMap.fmap ϕ (help t) a
  where
  a : fst C (suc (fst x))
  a = FinSequence.fmap (realiseFinSeq m C) r
  help : fsuc (injectSuc x) ≡ injectSuc (fsuc x)
  help = Σ≡Prop (λ _ → isProp≤) refl

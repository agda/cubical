{-# OPTIONS --cubical --safe #-}
module Cubical.Foundations.Everything where

-- Basic cubical prelude
open import Cubical.Foundations.Prelude public

-- Definition of Identity types and definitions of J, funExt,
-- univalence and propositional truncation using Id instead of Path
open import Cubical.Foundations.Id
  hiding ( _≡_ ; _≡⟨_⟩_ ; _∎ )
  renaming ( _≃_           to EquivId
           ; EquivContr    to EquivContrId
           ; J             to JId
           ; ap            to apId
           ; equivFun      to equivFunId
           ; equivCtr      to equivCtrId
           ; fiber          to fiberId
           ; funExt        to funExtId
           ; isContr       to isContrId
           ; isProp        to isPropId
           ; isSet         to isSetId
           ; isEquiv       to isEquivId
           ; equivIsEquiv  to equivIsEquivId
           ; refl           to reflId
           ; ∥_∥           to propTruncId
           ; ∣_∣           to incId
           ; isPropIsContr to isPropIsContrId
           ; isPropIsEquiv to isPropIsEquivId
           )

open import Cubical.Foundations.GroupoidLaws public
open import Cubical.Foundations.CartesianKanOps public
open import Cubical.Foundations.Function public
open import Cubical.Foundations.Equiv public
open import Cubical.Foundations.PathSplitEquiv public
open import Cubical.Foundations.FunExtEquiv public
open import Cubical.Foundations.HLevels public
open import Cubical.Foundations.Path public
open import Cubical.Foundations.Transport public
open import Cubical.Foundations.Univalence public
open import Cubical.Foundations.UnivalenceId public
open import Cubical.Foundations.GroupoidLaws public
open import Cubical.Foundations.Isomorphism public
open import Cubical.Foundations.Logic
open import Cubical.Foundations.HoTT-UF

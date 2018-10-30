{-# OPTIONS --cubical #-}
module Cubical.Everything where

-- Basic primitives (some are from Agda.Primitive)
open import Cubical.Core public

-- Basic cubical prelude
open import Cubical.Prelude public

-- Propositional truncation defined as a higher inductive type
open import Cubical.PropositionalTruncation public

-- Definition of equivalences, Glue types and the univalence theorem
open import Cubical.Glue public

-- Definition of Identity types and definitions of J, funExt,
-- univalence and propositional truncation using Id instead of Path
open import Cubical.Id public
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
           ; ∣_∣           to incId )

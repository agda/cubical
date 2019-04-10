{-# OPTIONS --cubical --safe #-}
module Cubical.Core.Everything where

-- Basic primitives (some are from Agda.Primitive)
open import Cubical.Core.Primitives public

-- Basic cubical prelude
open import Cubical.Core.Prelude public

-- Definition of equivalences, Glue types and the univalence theorem
open import Cubical.Core.Glue public

-- Propositional truncation defined as a higher inductive type
open import Cubical.Core.PropositionalTruncation public

-- Definition of Identity types and definitions of J, funExt,
-- univalence and propositional truncation using Id instead of Path
open import Cubical.Core.Id
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

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

-- Definition of Identity types
open import Cubical.Id public
  hiding ( _≡_ ; ≡-proof_ ; begin_ ; _≡⟨⟩_ ; _≡⟨_⟩_ ; _≡-qed ; _∎ )
  renaming ( _≃_           to EquivId
           ; EquivContr    to EquivContrId
           ; J             to JId
           ; cong          to congId
           ; equivFun      to equivFunId
           ; equivCtr      to equivCtrId
           ; fiber         to fiberId
           ; funExt        to funExtId
           ; isContr       to isContrId
           ; isProp        to isPropId
           ; isSet         to isSetId
           ; isEquiv       to isEquivId
           ; equivIsEquiv  to equivIsEquivId
           ; refl          to reflId
           ; sym           to symId
           ; ∥_∥           to propTruncId
           ; ∣_∣           to incId
           ; squash        to squashId
           ; recPropTrunc  to recPropTruncId
           ; elimPropTrunc to elimPropTruncId )

{-# OPTIONS --safe #-}
module Cubical.Relation.Nullary.DecidablePropositions where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.Properties

private
  variable
    ℓ  : Level

DecProp : (ℓ : Level) → Type (ℓ-suc ℓ)
DecProp ℓ = Σ[ P ∈ hProp ℓ ] Dec (P .fst)

isSetDecProp : isSet (DecProp ℓ)
isSetDecProp = isOfHLevelΣ 2 isSetHProp (λ P → isProp→isSet (isPropDec (P .snd)))

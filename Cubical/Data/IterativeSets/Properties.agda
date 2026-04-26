module Cubical.Data.IterativeSets.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Relation.Nullary
open import Cubical.Data.Empty renaming (elim* to ⊥*-elim)
open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Data.Bool.Properties

open import Cubical.Data.IterativeSets.Base

private
  variable
    ℓ : Level


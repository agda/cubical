module Cubical.Data.IterativeSets.Bool where

open import Cubical.Foundations.Prelude

open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Functions.Embedding
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary using (¬_)

-- TODO: remove ⊥*-elim, Data.Unit, Data.SumFin once the statements that need them have found their way to a better place
open import Cubical.Data.Empty renaming (elim* to ⊥*-elim ; elim to ⊥-elim)
open import Cubical.Data.Bool
open import Cubical.Data.Unit.Properties

open import Cubical.Data.IterativeSets.Base
open import Cubical.Data.IterativeSets.UnorderedPair.Base
open import Cubical.Data.IterativeSets.Empty
open import Cubical.Data.IterativeSets.Unit
open import Cubical.Data.IterativeSets.Singleton.Properties

private
  variable
    ℓ : Level

bool⁰ : V⁰ {ℓ}
bool⁰ {ℓ} = unorderedPair⁰ empty⁰ unit⁰ empty⁰≢unit⁰

bool⁰IsBool : El⁰ {ℓ} bool⁰ ≡ Bool* {ℓ}
bool⁰IsBool = refl

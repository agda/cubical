{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Homotopy.EilenbergSteenrod where

open import Cubical.Core.Everything

open import Cubical.Data.Nat

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws
open import Cubical.HITs.SetTruncation
open import Cubical.HITs.Truncation hiding (elim2) renaming (rec to trRec)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv.HalfAdjoint
open Iso

open import Cubical.HITs.Pushout
open import Cubical.HITs.Susp

record satES-axioms {ℓ ℓ' : Level} (A : Type ℓ) (H : (n : ℕ) → A → Type ℓ) : Type (ℓ-max ℓ ℓ') where
  field
    Exact : A
    Exacts : A → ℕ → {!!}

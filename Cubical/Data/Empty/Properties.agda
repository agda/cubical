{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Data.Empty.Properties where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude

open import Cubical.Data.Empty.Base

isProp⊥ : isProp ⊥
isProp⊥ ()

isContr⊥→A : ∀ {ℓ} {A : Type ℓ} → isContr (⊥ → A)
fst isContr⊥→A ()
snd isContr⊥→A f i ()

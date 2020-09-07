{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Data.Unit.Base where
open import Cubical.Foundations.Prelude

-- Obtain Unit
open import Agda.Builtin.Unit public
  renaming ( ⊤ to Unit )

-- Lifted version
data Unit* {ℓ : Level} : Type ℓ where
  tt* : Unit*

{-# OPTIONS --safe #-}
module Cubical.Data.Unit.Base where
open import Cubical.Foundations.Prelude

-- Obtain Unit
open import Agda.Builtin.Unit public
  renaming ( ⊤ to Unit )

-- Universe polymorphic version
Unit* : {ℓ : Level} → Type ℓ
Unit* = Lift Unit

pattern tt* = lift tt

-- Universe polymorphic version without definitional equality
-- Allows us to "lock" proofs. See "Locking, unlocking" in
-- https://coq.inria.fr/refman/proof-engine/ssreflect-proof-language.html
data lockUnit {ℓ} : Type ℓ where
  unlock : lockUnit

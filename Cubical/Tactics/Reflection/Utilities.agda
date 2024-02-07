{-# OPTIONS --safe #-}
module Cubical.Tactics.Reflection.Utilities where

open import Cubical.Foundations.Prelude hiding (Type)

open import Agda.Builtin.Reflection hiding (Type)
open import Agda.Builtin.String
open import Agda.Builtin.Nat using () renaming (_==_ to _=ℕ_)

open import Cubical.Reflection.Base
open import Cubical.Data.List
open import Cubical.Data.Maybe
open import Cubical.Data.FinData using () renaming (zero to fzero; suc to fsuc)
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ)

open import Cubical.Tactics.Reflection
open import Cubical.Tactics.Reflection.Variables


finiteNumberAsTerm : Maybe ℕ → Term
finiteNumberAsTerm (just ℕ.zero) = con (quote fzero) []
finiteNumberAsTerm (just (ℕ.suc n)) = con (quote fsuc) (finiteNumberAsTerm (just n) v∷ [])
finiteNumberAsTerm _ = unknown

-- error message helper
errorOut : List (Arg Term) → TC (Template × Vars)
errorOut something = typeError (strErr "Don't know what to do with " ∷ map (λ {(arg _ t) → termErr t}) something)

errorOut' : Term → TC (Template × Vars)
errorOut' something = typeError (strErr "Don't know what to do with " ∷ termErr something ∷ [])


_==_ = primQNameEquality
{-# INLINE _==_ #-}

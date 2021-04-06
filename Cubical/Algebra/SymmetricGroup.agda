{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.SymmetricGroup where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ ; suc ; zero)
open import Cubical.Data.Fin using (Fin ; isSetFin)
open import Cubical.Data.Empty
open import Cubical.Relation.Nullary using (¬_)

open import Cubical.Algebra.Group

private
  variable
    ℓ : Level

Symmetric-Group : (X : Type ℓ) → isSet X → Group {ℓ}
Symmetric-Group X isSetX = makeGroup (idEquiv X) compEquiv invEquiv (isOfHLevel≃ 2 isSetX isSetX)
  compEquiv-assoc compEquivEquivId compEquivIdEquiv invEquiv-is-rinv invEquiv-is-linv

-- Finite symmetrics groups

Sym : ℕ → Group
Sym n = Symmetric-Group (Fin n) isSetFin

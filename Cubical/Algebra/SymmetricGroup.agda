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

open import Cubical.Data.Group hiding (_≃_)
open import Cubical.Structures.NAryOp

private
  variable
    ℓ : Level

Symmetric-Group : (X : Type ℓ) → isSet X → Group ℓ
Symmetric-Group X isSetX =
  group (X ≃ X) (isOfHLevel≃ 2 isSetX isSetX)
        (group-struct (idEquiv X) invEquiv compEquiv compEquivIdEquiv compEquivEquivId
                      (λ a b c → sym (compEquiv-assoc a b c)) invEquiv-is-linv invEquiv-is-rinv)

-- Finite symmetrics groups

Sym : ℕ → Group _
Sym n = Symmetric-Group (Fin n) isSetFin

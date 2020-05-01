{-# OPTIONS --cubical --safe #-}
module Cubical.Algebra.SymmetricGroup where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ ; suc ; zero)
open import Cubical.Data.Fin using (Fin ; isSetFin)
open import Cubical.Data.Empty
open import Cubical.Relation.Nullary using (¬_)

open import Cubical.Structures.Group
open import Cubical.Structures.NAryOp

private
  variable
    ℓ ℓ' : Level

Symmetric-Group : (X : Type ℓ) → isSet X → Group
Symmetric-Group X isSetX =
  (X ≃ X) ,
  compEquiv ,
  (isOfHLevel≃ 2 isSetX isSetX , compEquiv-assoc) ,
  idEquiv X , (λ f → compEquivEquivId f , compEquivIdEquiv f) , λ f → invEquiv f , invEquiv-is-rinv f , invEquiv-is-linv f

-- Finite symmetrics groups

Sym : ℕ → Group
Sym n = Symmetric-Group (Fin n) isSetFin

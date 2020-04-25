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

private
  variable
    ℓ ℓ' : Level

infixr 20 _∘_

_∘_ : {A B C : Type ℓ} → B ≃ C → A ≃ B → A ≃ C
g ∘ f = compEquiv f g

∘-assoc : {A B C D : Type ℓ} (h : C ≃ D) (g : B ≃ C) (f : A ≃ B)
        → h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f
∘-assoc h g f = equivEq _ _ refl

Symmetric-Group : (X : Type ℓ) → isSet X → Group
Symmetric-Group X isSetX =
  (X ≃ X) ,
  _∘_ ,
  (isOfHLevel≃ 2 isSetX isSetX , ∘-assoc) ,
  idEquiv X , (λ f → compEquivIdEquiv f , compEquivEquivId f) , λ f → invEquiv f , invEquiv-is-linv f , invEquiv-is-rinv f

-- Finite symmetrics groups
Sym : ℕ → Group
Sym n = Symmetric-Group (Fin n) isSetFin

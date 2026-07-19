{-

This file contains:

- Definition of groupoid quotients

-}
{-# OPTIONS --cubical --no-import-sorts #-}
module Cubical.HITs.GroupoidQuotients.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Binary.Base

-- Groupoid quotients as a higher inductive type:
-- For the definition, only transitivity is needed
data _//_ {ℓ ℓ'} (A : Type ℓ) {R : A → A → Type ℓ'}
          (Rt : BinaryRelation.isTrans R) : Type (ℓ-max ℓ ℓ') where
  [_] : (a : A) → A // Rt
  eq// : {a b : A} → (r : R a b) → [ a ] ≡ [ b ]
  comp// : {a b c : A} → (r : R a b) → (s : R b c)
          → PathP (λ j → [ a ] ≡ eq// s j) (eq// r) (eq// (Rt a b c r s))
  squash// : ∀ (x y : A // Rt) (p q : x ≡ y) (r s : p ≡ q) → r ≡ s

{- The comp// constructor fills the square:

  eq// (Rt a b c r s)
    [a]— — — >[c]
     ‖         ^
     ‖         | eq// s   ^
     ‖         |        j |
    [a]— — — >[b]         ∙ — >
       eq// r               i

  We use this to give another constructor-like construction:
-}

comp'// : {ℓ ℓ' : Level} (A : Type ℓ) {R : A → A → Type ℓ'}
          (Rt : BinaryRelation.isTrans R)
          {a b c : A} → (r : R a b) → (s : R b c)
          → eq// {Rt = Rt} (Rt a b c r s) ≡ eq// r ∙ eq// s
comp'// A Rt r s i = compPath-unique refl (eq// r) (eq// s)
  (eq// {Rt = Rt} (Rt _ _ _ r s) , comp// r s)
  (eq// r ∙ eq// s , compPath-filler (eq// r) (eq// s)) i .fst

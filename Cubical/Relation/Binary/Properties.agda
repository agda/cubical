{-# OPTIONS --safe #-}
module Cubical.Relation.Binary.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Binary.Base

private
  variable
    ℓ : Level
    A B : Type ℓ


-- Pulling back a relation along a function.

module _
  (f : A → B)
  (R : Rel B B ℓ)
  where

  open BinaryRelation

  on : Rel A A ℓ
  on x y = R (f x) (f y)

  isReflOn : isRefl R → isRefl on
  isReflOn isReflR a = isReflR (f a)

  isSymOn : isSym R → isSym on
  isSymOn isSymR a a' = isSymR (f a) (f a')

  isTransOn : isTrans R → isTrans on
  isTransOn isTransR a a' a'' = isTransR (f a) (f a') (f a'')

  open isEquivRel

  isEquivRelOn : isEquivRel R → isEquivRel on
  reflexive (isEquivRelOn isEquivRelR) = isReflOn (reflexive isEquivRelR)
  symmetric (isEquivRelOn isEquivRelR) = isSymOn (symmetric isEquivRelR)
  transitive (isEquivRelOn isEquivRelR) = isTransOn (transitive isEquivRelR)

{-# OPTIONS --safe #-}
module Cubical.Relation.Binary.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Binary.Base

private
  variable
    ℓ : Level
    A B : Type ℓ


-- Pulling back a relation along a function.
-- This can for example be used when restricting an equivalence relation to a subset:
--   _~'_ = on fst _~_

module _
  (f : A → B)
  (R : Rel B B ℓ)
  where

  open BinaryRelation

  pulledbackRel : Rel A A ℓ
  pulledbackRel x y = R (f x) (f y)

  isReflPulledbackRel : isRefl R → isRefl pulledbackRel
  isReflPulledbackRel isReflR a = isReflR (f a)

  isSymPulledbackRel : isSym R → isSym pulledbackRel
  isSymPulledbackRel isSymR a a' = isSymR (f a) (f a')

  isTransPulledbackRel : isTrans R → isTrans pulledbackRel
  isTransPulledbackRel isTransR a a' a'' = isTransR (f a) (f a') (f a'')

  open isEquivRel

  isEquivRelPulledbackRel : isEquivRel R → isEquivRel pulledbackRel
  reflexive (isEquivRelPulledbackRel isEquivRelR) = isReflPulledbackRel (reflexive isEquivRelR)
  symmetric (isEquivRelPulledbackRel isEquivRelR) = isSymPulledbackRel (symmetric isEquivRelR)
  transitive (isEquivRelPulledbackRel isEquivRelR) = isTransPulledbackRel (transitive isEquivRelR)

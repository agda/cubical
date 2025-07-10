{-# OPTIONS --safe #-}
{-
CW structure on joins
-}

module Cubical.CW.Instances.Join where

open import Cubical.Foundations.Prelude

open import Cubical.CW.Base
open import Cubical.CW.Instances.Pushout
open import Cubical.CW.Instances.Sigma

open import Cubical.HITs.Join

-- joins as finite CW complexes
isFinCWJoinPushout : (A B : finCW ℓ-zero)
  → isFinCW (joinPushout (fst A) (fst B))
isFinCWJoinPushout A B = isFinCWPushout (_ , (isFinCW× A B)) A B fst snd

isFinCWJoin : (A B : finCW ℓ-zero) → isFinCW (join (fst A) (fst B))
isFinCWJoin A B =
  subst isFinCW (joinPushout≡join (fst A) (fst B)) (isFinCWJoinPushout A B)

-- todo: joins of arbitrary complexes

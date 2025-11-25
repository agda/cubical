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
isFinCWJoinPushout : {ℓ : Level} (A B : finCW ℓ)
  → isFinCW (joinPushout (fst A) (fst B))
isFinCWJoinPushout A B = isFinCWPushout (_ , (isFinCW× A B)) A B fst snd

isFinCWJoin : {ℓ : Level} (A B : finCW ℓ) → isFinCW (join (fst A) (fst B))
isFinCWJoin A B =
  subst isFinCW (joinPushout≡join (fst A) (fst B)) (isFinCWJoinPushout A B)

-- todo: joins of arbitrary complexes

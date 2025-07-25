
module Cubical.HITs.DunceCap.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws

open import Cubical.HITs.S1 using (S¹; base)
import Cubical.HITs.S1 as S¹

open import Cubical.HITs.MappingCones

-- definition of the dunce cap as a HIT

data Dunce : Type₀ where
  base : Dunce
  loop : base ≡ base
  surf : PathP (λ i → loop i ≡ loop i) loop refl

-- definition of the dunce cap as a mapping cone

dunceMap : S¹ → S¹
dunceMap base        = base
dunceMap (S¹.loop i) = (S¹.loop ⁻¹ ∙∙ S¹.loop ∙∙ S¹.loop) i

DunceCone : Type₀
DunceCone = Cone dunceMap

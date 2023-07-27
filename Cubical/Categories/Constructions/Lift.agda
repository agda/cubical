{-# OPTIONS --safe #-}
module Cubical.Categories.Constructions.Lift where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Categories.Category
open import Cubical.Categories.Functor

private
  variable
    ℓ ℓ' : Level

open Category

module _ (C : Category ℓ ℓ') (ℓ'' : Level) where
  LiftHoms : Category ℓ (ℓ-max ℓ' ℓ'')
  LiftHoms .ob = C .ob
  LiftHoms .Hom[_,_] A B = Lift {j = ℓ''} (C [ A , B ])
  LiftHoms .id = lift (C .id)
  LiftHoms ._⋆_ f g = lift (f .lower ⋆⟨ C ⟩ g .lower)
  LiftHoms .⋆IdL f = cong lift (C .⋆IdL (f .lower))
  LiftHoms .⋆IdR f = cong lift (C .⋆IdR (f .lower))
  LiftHoms .⋆Assoc f g h = cong lift (C .⋆Assoc (f .lower) (g .lower) (h .lower))
  LiftHoms .isSetHom = isOfHLevelLift 2 (C .isSetHom)

  liftHoms : Functor C LiftHoms
  liftHoms .Functor.F-ob = λ z → z
  liftHoms .Functor.F-hom = lift
  liftHoms .Functor.F-id = refl
  liftHoms .Functor.F-seq f g = refl

  lowerHoms : Functor LiftHoms C
  lowerHoms .Functor.F-ob = λ z → z
  lowerHoms .Functor.F-hom = lower
  lowerHoms .Functor.F-id = refl
  lowerHoms .Functor.F-seq f g = refl

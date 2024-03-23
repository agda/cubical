{-# OPTIONS --safe #-}
module Cubical.Algebra.AbGroup.Instances.Pi where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group.Instances.Pi

module _ {ℓ ℓ' : Level} {X : Type ℓ} (G : X → AbGroup ℓ') where
  ΠAbGroup : AbGroup (ℓ-max ℓ ℓ')
  ΠAbGroup = Group→AbGroup (ΠGroup (λ x → AbGroup→Group (G x)))
              λ f g i x → IsAbGroup.+Comm (AbGroupStr.isAbGroup (G x .snd)) (f x) (g x) i

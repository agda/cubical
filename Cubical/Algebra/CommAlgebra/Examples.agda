{-# OPTIONS --cubical --safe --no-import-sorts #-}
module Cubical.Algebra.CommAlgebra.Examples where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommAlgebra.Base

private
  variable
    ℓ : Level

module CommAlgebraExamples ((R , str) : CommRing {ℓ}) where
  open CommRingStr str
  initial : CommAlgebra (R , str)
  initial = commalgebra R 0r 1r _+_ _·_ -_ (λ r x → r · x)
                    (makeIsCommAlgebra (isSetRing (CommRing→Ring (R , str)))
                       +Assoc +Rid +Rinv +Comm
                       ·Assoc ·Lid
                       ·Ldist+ ·-comm
                        (λ x y z → sym (·Assoc x y z)) ·Ldist+ ·Rdist+ ·Lid λ x y z → sym (·Assoc x y z))




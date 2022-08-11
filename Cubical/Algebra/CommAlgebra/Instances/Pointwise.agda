{-# OPTIONS --safe #-}
module Cubical.Algebra.CommAlgebra.Instances.Pointwise where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Algebra.CommRing.Base
open import Cubical.Algebra.CommRing.Instances.Pointwise
open import Cubical.Algebra.CommAlgebra.Base

private
  variable
    ℓ : Level

pointwiseAlgebra :  {R : CommRing ℓ} (X : Type ℓ) (A : CommAlgebra R ℓ) → CommAlgebra R ℓ
pointwiseAlgebra {R = R} X A =
  let open CommAlgebraStr (snd A)
      isSetX→A = isOfHLevelΠ 2 (λ (x : X) → isSetCommRing (CommAlgebra→CommRing A))
  in commAlgebraFromCommRing
       (pointwiseRing X (CommAlgebra→CommRing A))
       (λ r f → (λ x → r ⋆ (f x)))
       (λ r s f i x → ⋆Assoc r s (f x) i)
       (λ r f g i x → ⋆DistR+ r (f x) (g x) i)
       (λ r s f i x → ⋆DistL+ r s (f x) i)
       (λ f i x → ⋆IdL (f x) i)
       λ r f g i x → ⋆AssocL r (f x) (g x) i

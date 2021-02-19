{-# OPTIONS --cubical --safe --no-import-sorts #-}
module Cubical.Algebra.CommAlgebra.QuotientAlgebra where
open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.QuotientRing renaming (_/_ to _/Ring_)
open import Cubical.Algebra.CommAlgebra
open import Cubical.Algebra.CommAlgebra.Ideal

private
  variable
    ℓ : Level

_/_ : {R : CommRing {ℓ}} (A : CommAlgebra R) → (I : IdealsIn A) → CommAlgebra R
A / I = {!(CommRing→Ring (CommAlgebra→CommRing A)) /Ring I!}

[_]/ : {R : CommRing {ℓ}} {A : CommAlgebra R} {I : IdealsIn A} → (a : CommAlgebra.Carrier A) → CommAlgebra.Carrier (A / I)
[ a ]/ = [ a ]/I

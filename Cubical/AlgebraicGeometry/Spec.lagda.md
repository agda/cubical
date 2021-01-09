Synthetic Algebraic Geometry
============================

The Synthetic Spectrum
----------------------

Everything done here is from Ingo Blechschmidt's thesis or unpublished work of David Jaz Myers.


<!--
```
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.AlgebraicGeometry.Spec where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommAlgebra
open import Cubical.Algebra.CommAlgebra.Examples
open import Cubical.Algebra.Algebra

private
  variable
    ℓ : Level

```
-->

In the following, we will use a fixed, commutative ring 𝔸.
We are specifically interested in commutative algebras over that ring, so let us introduce a short name for those.

```

module _ (𝔸asRing : CommRing {ℓ}) where
  𝔸-Alg = CommAlgebra 𝔸asRing
  𝔸 = CommAlgebraExamples.initial 𝔸asRing

```

The synthetic spectrum of an 𝔸-algebra R, Spec R, is supposed to be a space such that
the ring of functions on Spec R is R. Moreover, Spec R, should be so small and rigid,
that the only homomorphisms R → 𝔸 are evaluations at points.
The latter can be turned around to give a definition:

```

  Hom : 𝔸-Alg → 𝔸-Alg → Type ℓ
  Hom R S = CAlgHom R S

  Spec : 𝔸-Alg → Type ℓ
  Spec R = Hom R 𝔸

```

𝔸 is the initial 𝔸-algebra, so we now that its spectrum has to be equal to the point:

```

  point : Type ℓ
  point = Unit*

  _ : Spec 𝔸 ≡ point
  _ = CommAlgebraExamples.isInitial 𝔸asRing 𝔸

```

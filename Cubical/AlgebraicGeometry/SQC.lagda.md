Synthetic Algebraic Geometry
============================

Synthetic quasi coherence
-------------------------

Everything done here is from Ingo Blechschmidt's thesis or unpublished work of David Jaz Myers.

<!--
```
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.AlgebraicGeometry.SQC where

open import Cubical.Foundations.Everything
open import Cubical.Data.Unit

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommAlgebra
open import Cubical.Algebra.CommAlgebra.Examples
open import Cubical.Algebra.CommAlgebra.FreeCommAlgebra
open import Cubical.Algebra.CommAlgebra.Morphism
open import Cubical.Algebra.Algebra

open import Cubical.AlgebraicGeometry.Spec

private
  variable
    ℓ : Level

```
-->

Let 𝔸 be a commutative ring, and let us use the same notation as in [Spec](Spec.lagda.md)
```
module _ (𝔸asRing : CommRing {ℓ}) where
  open SpecExamples 𝔸asRing
```
For any algebra R over 𝔸, there is a map from R to 𝔸-valued functions on Spec R:
```
  evMap : {R : 𝔸-Alg} → CommAlgebra.Carrier R → (Spec R → 𝔸′)
  evMap r = λ f → (AlgebraHom.map f) r
```

The Synthetic Spectrum
----------------------

All the mathematics presented here, is from [Ingo Blechschmidt](https://www.ingo-blechschmidt.eu/research.html)'s thesis or unpublished work of [David Jaz Myers](http://davidjaz.com/). The formalization in Agda are due to [Felix Cherubini](http://felix-cherubini.de).


<!--
```
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.AlgebraicGeometry.Spec where

open import Cubical.Foundations.Everything
open import Cubical.Data.Unit
open import Cubical.Data.FinData
open import Cubical.Data.Nat
open import Cubical.Data.Vec

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommAlgebra
open import Cubical.Algebra.CommAlgebra.Examples
open import Cubical.Algebra.CommAlgebra.FreeCommAlgebra
open import Cubical.Algebra.CommAlgebra.Morphism
open import Cubical.Algebra.Algebra

private
  variable
    ℓ : Level

```
-->

In the following, we will use a fixed, commutative ring 𝔸.
We are specifically interested in commutative algebras over that ring, so let us introduce a short name for those
and let us use '𝔸' to refer to the 𝔸-algebra 𝔸.

```

module SpecExamples (𝔸asRing : CommRing {ℓ}) where
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

𝔸 is the initial 𝔸-algebra, so we know that its spectrum has to be equal to the point:

```

  point : Type ℓ
  point = Unit*

  _ : Spec 𝔸 ≡ point
  _ = CommAlgebraExamples.isInitial 𝔸asRing 𝔸

```

Note that in the Zariski topos based on affine k-schemes, Spec k would be the point as well.
In general, 𝔸 behaves like the base field (or ring) when plugged into the Spec construction.
Here is another instance of this phenomenon:

```

  𝔸[X] = 𝔸asRing [ Unit* ]
  𝔸′ = CommAlgebra.Carrier 𝔸              -- 𝔸′ is the underlying type of the algebra 𝔸

  _ : Spec 𝔸[X] ≡ 𝔸′
  _ = Spec 𝔸[X]        ≡⟨ refl ⟩
      Hom 𝔸[X] 𝔸      ≡⟨ homMapEq 𝔸 ⟩
      (Unit* → 𝔸′)     ≡⟨ isoToPath
                            (iso (λ f → f tt*) (λ a _ → a)
                                 (λ b i → b)
                                 λ a i x → a x) ⟩
      𝔸′ ∎

```
More generall, any type of the form 'D → 𝔸' is a 'Spec' of the 𝔸-algebra 𝔸[D]:

```
  module _ (D : Type ℓ) where
    𝔸[D] = 𝔸asRing [ D ]
    mappingSchemeEq : Spec 𝔸[D] ≡ (D → 𝔸′)
    mappingSchemeEq = Spec 𝔸[D]      ≡⟨ refl ⟩
                      Hom 𝔸[D] 𝔸    ≡⟨ homMapEq 𝔸 ⟩
                      (D → 𝔸′)       ∎
```
We can use the standard n-elment type 'Fin n'
to define the affine n-dimensional standard space as a spectrum:

```
  𝔸″ : ℕ → Type ℓ
  𝔸″ n = Spec (𝔸asRing [ Lift (Fin n) ])
```
This space is equivalent to a mapping space as we showed above, which in turn is
a cartesian product. For the n-fold cartesian product of 𝔸, we use the type 'Vec 𝔸 n':

```
  standardSpaceEq : ∀ (n : ℕ)
                  → 𝔸″ n ≡ Vec 𝔸′ n
  standardSpaceEq n = 𝔸″ n                ≡⟨ mappingSchemeEq _ ⟩
                      (Lift (Fin n) → 𝔸′) ≡⟨ lemma _ _ LiftEquiv ⟩
                      (Fin n → 𝔸′)        ≡⟨ FinVec≡Vec n ⟩
                      Vec 𝔸′ n ∎
    where lemma : (X : Type₀) (Y : Type ℓ) → (X ≃ Y) → (Y → 𝔸′) ≡ (X → 𝔸′)
          lemma X Y equiv =
            let open Iso (equivToIso equiv)
                  renaming (fun to e; inv to e⁻¹)
            in isoToPath
               (iso (λ f → λ x → f (e x))
                    (λ g → λ y → g (e⁻¹ y))
                    (λ f → λ i x →
                         (f (e⁻¹ (e x)) ≡⟨ cong f (leftInv x) ⟩
                         f x            ∎)
                      i)
                    λ g → λ i y →
                         (g (e (e⁻¹ y)) ≡⟨ cong g (rightInv y) ⟩
                         g y ∎)
                       i)
```

See how the story is supposed to continue with [Synthetic Quasi Coherence](Cubical.AlgebraicGeometry.SQC.html).

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
open import Cubical.Foundations.HLevels
open import Cubical.Data.Unit

open import Cubical.Algebra.Ring
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

Let 𝔸 be a commutative ring, and let us use the same notation as in [Spec](Cubical.AlgebraicGeometry.Spec.html)

```
module _ (𝔸asRing : CommRing {ℓ}) where
  open SpecExamples 𝔸asRing
```
For any algebra R over 𝔸, there is a map from R to 𝔸-valued functions on Spec R:

```
  evMap : (R : 𝔸-Alg) → CommAlgebra.Carrier R → (Spec R → 𝔸′)
  evMap _ r = λ f → (AlgebraHom.map f) r
```
This is also a homomorphism of rings. To make that statement,
we have to define a ring structure on the 𝔸-valued functions.
Let us first construct the pointwise ring structure in general:

```
  pointwiseRingStructure : (X : Type ℓ) (R : CommRing {ℓ}) → CommRing {ℓ}
  pointwiseRingStructure X R =
    let open CommRingStr (snd R)
        isSetX→R = isOfHLevelΠ 2 (λ _ → isSetCommRing R)
    in (X → fst R) ,
       (commringstr
         (λ _ → 0r) (λ _ → 1r)
         (λ f g → (λ x → f x + g x))
         (λ f g → (λ x → f x · g x))
         (λ f → (λ x → - f x))
         (makeIsCommRing
           isSetX→R
           (λ f g h i x → +Assoc (f x) (g x) (h x) i)
           (λ f i x → +Rid (f x) i)
           (λ f i x → +Rinv (f x) i)
           (λ f g i x → +Comm (f x) (g x) i)
           (λ f g h i x → ·Assoc (f x) (g x) (h x) i)
           (λ f i x → ·Rid (f x) i)
           (λ f g h i x → ·Rdist+ (f x) (g x) (h x) i)
           λ f g i x → ·-comm (f x) (g x) i))
```
This can be extended to an algebra structure:

```
  pointwiseAlgebra :  {R : CommRing {ℓ}} (X : Type ℓ) (A : CommAlgebra R) → CommAlgebra R
  pointwiseAlgebra X A =
    let open CommAlgebra A
        isSetX→A = isOfHLevelΠ 2 (λ _ → isSetCommRing (CommAlgebra→CommRing A))
    in commalgebra (X → CommAlgebra.Carrier A)
      (λ _ → 0a) (λ _ → 1a)
      (λ f g → (λ x → f x + g x))
      (λ f g → (λ x → f x · g x))
      (λ f → (λ x → - f x))
      (λ r f → (λ x → CommAlgebra._⋆_ A r (f x)))
      (makeIsCommAlgebra isSetX→A
         (λ f g h i x → +-assoc (f x) (g x) (h x) i)
         (λ f i x → +-rid (f x) i) (λ f i x → +-rinv (f x) i)
         (λ f g i x → +-comm (f x) (g x) i)
         (λ f g h i x → ·Assoc (f x) (g x) (h x) i)
         (λ f i x → ·Lid (f x) i)
         (λ f g h i x → ·Ldist+ (f x) (g x) (h x) i)
         (λ f g i x → ·-comm (f x) (g x) i)
         (λ r s f i x → ⋆-assoc r s (f x) i)
         (λ r s f i x → ⋆-ldist r s (f x) i)
         (λ r f g i x → ⋆-rdist r (f x) (g x) i)
         (λ f i x → ⋆-lid (f x) i)
         λ r f g i x → ⋆-lassoc r (f x) (g x) i)
```
Now let us refer to the commutative ring of 𝔸-valued functions on a
type X with '𝒪′ X':

```
  𝒪′ : (X : Type ℓ) → CommRing {ℓ}
  𝒪′ X = pointwiseRingStructure X 𝔸asRing
```
And the algbera with '𝒪 X':

```
  𝒪 : (X : Type ℓ) → 𝔸-Alg
  𝒪 X = pointwiseAlgebra X 𝔸
```
Going back to where we started, we can now show that the evaluation map is a
homorphism of 𝔸-algberas:

```
  ev : {R : 𝔸-Alg} → Hom R (𝒪 (Spec R))
  ev {R = R} =
    let
      open CommAlgebra ⦃...⦄
      instance
        _ : 𝔸-Alg
        _ = 𝔸
        _ : 𝔸-Alg
        _ = R
    in algebrahom
         (evMap R)
                (λ r s i → λ {(algebrahom f +Hom _ _ _)
                     → (f (r + s) ≡⟨ +Hom _ _ ⟩ f r + f s ∎) i})
                (λ r s i → λ {(algebrahom f _ ·Hom _ _)
                     → (f (r · s) ≡⟨ ·Hom _ _ ⟩ f r · f s ∎) i})
                (λ i → λ {(algebrahom f _ _ pres1 _)
                     → (f 1a ≡⟨ pres1 ⟩ 1a ∎) i})
                λ r x i → λ {(algebrahom f +Hom _ _ ⋆Comm)
                  →               (f (CommAlgebra._⋆_ R r x)
                    ≡⟨ ⋆Comm _ _ ⟩ CommAlgebra._⋆_ 𝔸 r (f x) ∎) i}
```



module Cubical.Algebra.CommRing.Polynomials.Typevariate.Base where
{-
  The ring of polynomials with coefficients in a given ring,
  or in other words the free commutative algebra over a commutative ring.
  Note that this is a constructive definition, which entails that polynomials
  cannot be represented by lists of coefficients, where the last one is non-zero.
  For rings with decidable equality, that is still possible.

  I (Felix Cherubini) learned about this (and other) definition(s) from David Jaz Myers.
  You can watch him talk about these things here:
  https://www.youtube.com/watch?v=VNp-f_9MnVk

  This file contains
  * the definition of the free commutative algebra on a type I over a commutative ring R as a HIT
    (let us call that R[I])
  * the homomorphism R -> R[I], which turns this CommRing into a CommAlgebra
  For more, see the Properties file.
-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function using (_$_)

open import Cubical.Algebra.CommRing.Base

private
  variable
    ℓ ℓ' : Level

module Construction (R : CommRing ℓ) where
  open CommRingStr (snd R) using (1r; 0r) renaming (_+_ to _+r_; _·_ to _·r_)

  data R[_] (I : Type ℓ') : Type (ℓ-max ℓ ℓ') where
    var : I → R[ I ]
    const : fst R → R[ I ]
    _+_ : R[ I ] → R[ I ] → R[ I ]
    -_ : R[ I ] → R[ I ]
    _·_ : R[ I ] → R[ I ] → R[ I ]            -- \cdot

    +-assoc : (x y z : R[ I ]) → x + (y + z) ≡ (x + y) + z
    +-rid : (x : R[ I ]) → x + (const 0r) ≡ x
    +-rinv : (x : R[ I ]) → x + (- x) ≡ (const 0r)
    +-comm : (x y : R[ I ]) → x + y ≡ y + x

    ·-assoc : (x y z : R[ I ]) → x · (y · z) ≡ (x · y) · z
    ·-lid : (x : R[ I ]) → (const 1r) · x ≡ x
    ·-comm : (x y : R[ I ]) → x · y ≡ y · x

    ldist : (x y z : R[ I ]) → (x + y) · z ≡ (x · z) + (y · z)

    +HomConst : (s t : fst R) → const (s +r t) ≡ const s + const t
    ·HomConst : (s t : fst R) → const (s ·r t) ≡ (const s) · (const t)

    0-trunc : (x y : R[ I ]) (p q : x ≡ y) → p ≡ q

  opaque
    isCommRing : (I : Type ℓ') → IsCommRing (const {I = I} 0r) (const 1r) _+_ _·_ -_
    isCommRing I = makeOpaque $
      makeIsCommRing 0-trunc
                     +-assoc +-rid +-rinv +-comm
                      ·-assoc (λ x → ·-comm _ _ ∙ ·-lid x)
                      (λ x y z → (x · (y + z))       ≡⟨ ·-comm _ _ ⟩
                                 ((y + z) · x)       ≡⟨ ldist _ _ _ ⟩
                                 ((y · x) + (z · x)) ≡[ i ]⟨ (·-comm y x i + ·-comm z x i) ⟩
                                 ((x · y) + (x · z)) ∎)
                      ·-comm

  module _ (I : Type ℓ') where
    open CommRingStr hiding (isCommRing)
    commRingStr : CommRingStr (R[_] I)
    commRingStr .0r = _
    commRingStr .1r = _
    commRingStr .CommRingStr._+_ = _
    commRingStr .CommRingStr._·_ = _
    CommRingStr.- commRingStr = _
    commRingStr .CommRingStr.isCommRing = isCommRing I


  opaque
    open IsCommRingHom
    constIsCommRingHom : (I : Type ℓ') → IsCommRingHom (R .snd) (const {I = I}) (commRingStr I)
    constIsCommRingHom I = makeIsCommRingHom refl +HomConst ·HomConst

_[_] : (R : CommRing ℓ) (I : Type ℓ') → CommRing (ℓ-max ℓ ℓ')
fst (R [ I ]) = Construction.R[_] R I
snd (R [ I ]) = Construction.commRingStr R I

constPolynomial : (R : CommRing ℓ) (I : Type ℓ') → CommRingHom R (R [ I ])
constPolynomial R I .fst = let open Construction R
                           in R[_].const
constPolynomial R I .snd = Construction.constIsCommRingHom R I

opaque
  var : {R : CommRing ℓ} {I : Type ℓ'} → I → ⟨ R [ I ] ⟩
  var = Construction.var

{-# OPTIONS --cubical --safe #-}

module Cubical.Structures.FreeCommAlgebra where
{-
  The free commutative algebra over a commutative ring,
  or in other words the ring of polynomials with coefficients in a given ring.
  Note that this is a constructive definition, which entails that polynomials
  cannot be represented by lists of coefficients, where the last one is non-zero.
  For rings with decidable equality, that is still possible.

  I learned about this (and other) definition(s) from David Jaz Myers.
  You can watch him talk about these things here:
  https://www.youtube.com/watch?v=VNp-f_9MnVk
-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels

open import Cubical.Structures.CommRing
open import Cubical.Structures.Ring        using ()
open import Cubical.Structures.CommAlgebra renaming (⟨_⟩ to ⟨_⟩a)
open import Cubical.Structures.Algebra     hiding (⟨_⟩)

private
  variable
    ℓ ℓ′ : Level

module Construction (R : CommRing {ℓ}) where
  open CommRing R using (1r; 0r) renaming (_+_ to _+r_; _·_ to _·r_)

  data R[_] (I : Type ℓ′) : Type (ℓ-max ℓ ℓ′) where
    var : I → R[ I ]
    const : ⟨ R ⟩ → R[ I ]
    _+_ : R[ I ] → R[ I ] → R[ I ]
    -_ : R[ I ] → R[ I ]

    +-assoc : (x y z : R[ I ]) → x + (y + z) ≡ (x + y) + z
    +-rid : (x : R[ I ]) → x + (const 0r) ≡ x
    +-rinv : (x : R[ I ]) → x + (- x) ≡ (const 0r)
    +-comm : (x y : R[ I ]) → x + y ≡ y + x

    _·_ : R[ I ] → R[ I ] → R[ I ]            -- \cdot
    ·-assoc : (x y z : R[ I ]) → x · (y · z) ≡ (x · y) · z
    ·-lid : (x : R[ I ]) → (const 1r) · x ≡ x
    ·-comm : (x y : R[ I ]) → x · y ≡ y · x

    ldist : (x y z : R[ I ]) → (x + y) · z ≡ (x · z) + (y · z)

    +HomConst : (s t : ⟨ R ⟩) → const (s +r t) ≡ const s + const t
    ·HomConst : (s t : ⟨ R ⟩) → const (s ·r t) ≡ (const s) · (const t)

    0-trunc : (x y : R[ I ]) (p q : x ≡ y) → p ≡ q

  _⋆_ : {I : Type ℓ′} → ⟨ R ⟩ → R[ I ] → R[ I ]
  r ⋆ x = const r · x

  ⋆-assoc : {I : Type ℓ′} → (s t : ⟨ R ⟩) (x : R[ I ]) → (s ·r t) ⋆ x ≡ s ⋆ (t ⋆ x)
  ⋆-assoc s t x = const (s ·r t) · x       ≡⟨ cong (λ u → u · x) (·HomConst _ _) ⟩
                  (const s · const t) · x  ≡⟨ sym (·-assoc _ _ _) ⟩
                  const s · (const t · x)  ≡⟨ refl ⟩
                  s ⋆ (t ⋆ x) ∎

  ⋆-ldist-+ : {I : Type ℓ′} → (s t : ⟨ R ⟩) (x : R[ I ]) → (s +r t) ⋆ x ≡ (s ⋆ x) + (t ⋆ x)
  ⋆-ldist-+ s t x = (s +r t) ⋆ x             ≡⟨ cong (λ u → u · x) (+HomConst _ _) ⟩
                    (const s + const t) · x  ≡⟨ ldist _ _ _ ⟩
                    (s ⋆ x) + (t ⋆ x) ∎

  ⋆-rdist-+ : {I : Type ℓ′} → (s : ⟨ R ⟩) (x y : R[ I ]) → s ⋆ (x + y) ≡ (s ⋆ x) + (s ⋆ y)
  ⋆-rdist-+ s x y = const s · (x + y)             ≡⟨ ·-comm _ _ ⟩
                    (x + y) · const s             ≡⟨ ldist _ _ _ ⟩
                    (x · const s) + (y · const s) ≡⟨ cong (λ u → u + (y · const s)) (·-comm _ _) ⟩
                    (s ⋆ x) + (y · const s)       ≡⟨ cong (λ u → (s ⋆ x) + u) (·-comm _ _)  ⟩
                    (s ⋆ x) + (s ⋆ y) ∎

  ⋆-assoc-· : {I : Type ℓ′} → (s : ⟨ R ⟩) (x y : R[ I ]) → (s ⋆ x) · y ≡ s ⋆ (x · y)
  ⋆-assoc-· s x y = (s ⋆ x) · y ≡⟨ sym (·-assoc _ _ _) ⟩
                    s ⋆ (x · y) ∎

  0a : {I : Type ℓ′} → R[ I ]
  0a = (const 0r)

  1a : {I : Type ℓ′} → R[ I ]
  1a = (const 1r)

  isCommAlgebra : {I : Type ℓ} → IsCommAlgebra
                                   R {A = R[ I ]}
                                   0a 1a
                                   _+_ _·_ -_ _⋆_
  isCommAlgebra = makeIsCommAlgebra 0-trunc
                                    +-assoc +-rid +-rinv +-comm
                                    ·-assoc ·-lid ldist ·-comm
                                    ⋆-assoc ⋆-ldist-+ ⋆-rdist-+ ·-lid ⋆-assoc-·

_[_] : (R : CommRing {ℓ}) (I : Type ℓ) → CommAlgebra R
R [ I ] = let open Construction R
          in commalgebra R[ I ] 0a 1a _+_ _·_ -_ _⋆_ isCommAlgebra


module Theory {R : CommRing {ℓ}} {I : Type ℓ} where
  open CommRing R using (0r; 1r) renaming (_·_ to _·r_; ·-comm to ·r-comm)

  module _ (A : CommAlgebra R) (φ : I → ⟨ A ⟩a) where
    open CommAlgebra A
    open AlgebraTheory (CommRing→Ring R) (CommAlgebra→Algebra A)
    open Construction using (var; const) renaming (_+_ to _+c_; -_ to -c_; _·_ to _·c_)

    imageOf0Works : 0r ⋆ 1a ≡ 0a
    imageOf0Works = 0-actsNullifying 1a

    imageOf1Works : 1r ⋆ 1a ≡ 1a
    imageOf1Works = ⋆-lid 1a

    inducedMap : ⟨ R [ I ] ⟩a → ⟨ A ⟩a
    inducedMap (var x) = φ x
    inducedMap (const r) = r ⋆ 1a
    inducedMap (P +c Q) = (inducedMap P) + (inducedMap Q)
    inducedMap (-c P) = - inducedMap P
    inducedMap (Construction.+-assoc P Q S i) = +-assoc (inducedMap P) (inducedMap Q) (inducedMap S) i
    inducedMap (Construction.+-rid P i) =
      let
        eq : (inducedMap P) + (inducedMap (const 0r)) ≡ (inducedMap P)
        eq = (inducedMap P) + (inducedMap (const 0r)) ≡⟨ refl ⟩
             (inducedMap P) + (0r ⋆ 1a)               ≡⟨ cong
                                                         (λ u → (inducedMap P) + u)
                                                         (imageOf0Works) ⟩
             (inducedMap P) + 0a                      ≡⟨ +-rid _ ⟩
             (inducedMap P) ∎
      in eq i
    inducedMap (Construction.+-rinv P i) =
      let eq : (inducedMap P - inducedMap P) ≡ (inducedMap (const 0r))
          eq = (inducedMap P - inducedMap P) ≡⟨ +-rinv _ ⟩
               0a                            ≡⟨ sym imageOf0Works ⟩
               (inducedMap (const 0r))∎
      in eq i
    inducedMap (Construction.+-comm P Q i) = +-comm (inducedMap P) (inducedMap Q) i
    inducedMap (P ·c Q) = inducedMap P · inducedMap Q
    inducedMap (Construction.·-assoc P Q S i) = ·-assoc (inducedMap P) (inducedMap Q) (inducedMap S) i
    inducedMap (Construction.·-lid P i) =
      let eq = inducedMap (const 1r) · inducedMap P ≡⟨ cong (λ u → u · inducedMap P) imageOf1Works ⟩
               1a · inducedMap P                    ≡⟨ ·-lid (inducedMap P) ⟩
               inducedMap P ∎
      in eq i
    inducedMap (Construction.·-comm P Q i) = ·-comm (inducedMap P) (inducedMap Q) i
    inducedMap (Construction.ldist P Q S i) = ·-ldist-+ (inducedMap P) (inducedMap Q) (inducedMap S) i
    inducedMap (Construction.+HomConst s t i) = ⋆-ldist s t 1a i
    inducedMap (Construction.·HomConst s t i) =
      let eq = (s ·r t) ⋆ 1a       ≡⟨ cong (λ u → u ⋆ 1a) (·r-comm _ _) ⟩
               (t ·r s) ⋆ 1a       ≡⟨ ⋆-assoc t s 1a ⟩
               t ⋆ (s ⋆ 1a)        ≡⟨ cong (λ u → t ⋆ u) (sym (·-rid _)) ⟩
               t ⋆ ((s ⋆ 1a) · 1a) ≡⟨ ⋆-rassoc t (s ⋆ 1a) 1a ⟩
               (s ⋆ 1a) · (t ⋆ 1a) ∎
      in eq i
    inducedMap (Construction.0-trunc P Q p q i j) =
      isSetAlgebra (CommAlgebra→Algebra A) (inducedMap P) (inducedMap Q) (cong _ p) (cong _ q) i j

    inducedHom : AlgebraHom (CommAlgebra→Algebra (R [ I ])) (CommAlgebra→Algebra A)
    inducedHom = algebrahom
                   inducedMap
                   (λ x y → refl)
                   (λ x y → refl)
                   imageOf1Works
                   λ r x → (r ⋆ 1a) · inducedMap x ≡⟨ ⋆-lassoc r 1a (inducedMap x) ⟩
                           r ⋆ (1a · inducedMap x) ≡⟨ cong (λ u → r ⋆ u) (·-lid (inducedMap x)) ⟩
                           r ⋆ inducedMap x ∎

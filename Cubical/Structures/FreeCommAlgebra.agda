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

open import Cubical.Structures.CommRing    using (CommRing; ⟨_⟩)
open import Cubical.Structures.Ring        using ()
open import Cubical.Structures.Algebra     using (makeIsAlgebra) renaming (⟨_⟩ to ⟨_⟩r)
open import Cubical.Structures.CommAlgebra

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
    ·HomConst : (s t : ⟨ R ⟩) → const (s ·r t) ≡ const s · const t

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
  isCommAlgebra = makeIsCommAlgebra R 0-trunc
                                    +-assoc +-rid +-rinv +-comm
                                    ·-assoc ·-lid ldist ·-comm
                                    ⋆-assoc ⋆-ldist-+ ⋆-rdist-+ ·-lid ⋆-assoc-·

_[_] : (R : CommRing {ℓ}) (I : Type ℓ) → CommAlgebra R
R [ I ] = let open Construction R
          in commalgebra R[ I ] 0a 1a _+_ _·_ -_ _⋆_ isCommAlgebra

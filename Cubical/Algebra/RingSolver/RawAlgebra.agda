{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.RingSolver.RawAlgebra where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ)

open import Cubical.Algebra.RingSolver.AlmostRing hiding (⟨_⟩)
open import Cubical.Algebra.RingSolver.RawRing renaming (⟨_⟩ to ⟨_⟩ᵣ)
open import Cubical.Algebra.RingSolver.IntAsRawRing public
open import Cubical.Algebra.RingSolver.CommRingAsAlmostRing
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring
open import Cubical.Data.Int.Properties using (+-assoc; +-comm; pos0+) renaming (-_ to -ℤ_; _+_ to _+ℤ_)

private
  variable
    ℓ ℓ′ : Level

record RawAlgebra (R : RawRing {ℓ}) (ℓ′ : Level) : Type (ℓ-suc (ℓ-max ℓ ℓ′)) where

  constructor rawalgebra

  field
    Carrier : Type ℓ′
    scalar  : ⟨ R ⟩ᵣ → Carrier
    0r      : Carrier
    1r      : Carrier
    _+_     : Carrier → Carrier → Carrier
    _·_     : Carrier → Carrier → Carrier
    -_      : Carrier → Carrier

  infixl 8 _·_
  infixl 7 -_
  infixl 6 _+_

⟨_⟩ : {R : RawRing {ℓ}} → RawAlgebra R ℓ′ → Type ℓ′
⟨_⟩ = RawAlgebra.Carrier

module _ (A : AlmostRing {ℓ}) where
    open AlmostRing A

    scalarℕ : ℕ → Carrier
    scalarℕ ℕ.zero = 0r
    scalarℕ (ℕ.suc ℕ.zero) = 1r
    scalarℕ (ℕ.suc (ℕ.suc n)) = 1r + scalarℕ (ℕ.suc n)

{-
  Mapping to integer scalars and its (homorphism) properties.
-}
module _ (R : CommRing {ℓ}) where
    A = (CommRingAsAlmostRing R)
    open AlmostRing A

    scalarℤ : ℤ → Carrier
    scalarℤ (pos k)  = scalarℕ A k
    scalarℤ (negsuc k)  = - scalarℕ A (ℕ.suc k)

module _ (R : CommRing {ℓ}) where
  open Cubical.Algebra.Ring.Theory (CommRing→Ring R)
  open CommRingStr (snd R)

  scalar : ℤ → fst R
  scalar = scalarℤ R

  -DistScalar : (k : ℤ)
                → scalar (-ℤ k) ≡ - (scalar k)
  -DistScalar (pos ℕ.zero) = sym 0Selfinverse
  -DistScalar (pos (ℕ.suc n)) = refl
  -DistScalar (negsuc n) = sym (-Idempotent _)

  lemma : (k : ℤ)
          → scalar (sucInt k) ≡ 1r + scalar k
  lemma (pos ℕ.zero) = sym (+Rid _)
  lemma (pos (ℕ.suc ℕ.zero)) = refl
  lemma (pos (ℕ.suc (ℕ.suc n))) = refl
  lemma (negsuc ℕ.zero) = sym (+Rinv _)
  lemma (negsuc (ℕ.suc n)) =
    scalar (negsuc n)                        ≡⟨ sym (+Lid (scalar (negsuc n))) ⟩
    0r + scalar (negsuc n)                  ≡[ i ]⟨ +Rinv 1r (~ i) + scalar (negsuc n) ⟩
    (1r - 1r) + scalar (negsuc n)           ≡⟨ sym (+Assoc _ _ _) ⟩
    1r + (- 1r + - scalar (pos (ℕ.suc n))) ≡[ i ]⟨ 1r + -Dist 1r (scalar (pos (ℕ.suc n))) i ⟩
    1r + -(1r + scalar (pos (ℕ.suc n)))    ≡⟨ refl ⟩
    1r + -(scalar (pos (ℕ.suc (ℕ.suc n)))) ≡⟨ refl ⟩
    1r + scalar (negsuc (ℕ.suc n)) ∎

  +HomScalar : (k l : ℤ)
               → scalar (k +ℤ l) ≡ (scalar k) + (scalar l)
  +HomScalar (pos ℕ.zero) l =
             scalar (0 +ℤ l)       ≡[ i ]⟨ scalar (sym (pos0+ l) i) ⟩
             scalar l              ≡⟨ sym (+Lid _) ⟩
             0r + scalar l         ≡⟨ refl  ⟩
             scalar 0 + scalar l   ∎

  +HomScalar (pos (ℕ.suc ℕ.zero)) l =
    scalar (1 +ℤ l)                         ≡[ i ]⟨ scalar (+-comm 1 l i) ⟩
    scalar (l  +ℤ 1)                        ≡⟨ refl ⟩
    scalar (sucInt l)                       ≡⟨ lemma l ⟩
    1r + scalar l                           ≡⟨ refl ⟩
    scalar (pos (ℕ.suc ℕ.zero)) + scalar l ∎

  +HomScalar (pos (ℕ.suc (ℕ.suc n))) l =
    scalar (pos (ℕ.suc (ℕ.suc n)) +ℤ l)        ≡⟨ refl ⟩
    scalar ((pos (ℕ.suc n) +ℤ 1) +ℤ l)         ≡[ i ]⟨ scalar ((+-comm (pos (ℕ.suc n)) 1 i) +ℤ l) ⟩
    scalar ((1 +ℤ (pos (ℕ.suc n))) +ℤ l)       ≡[ i ]⟨ scalar (+-assoc 1 (pos (ℕ.suc n)) l (~ i)) ⟩
    scalar (1 +ℤ (pos (ℕ.suc n) +ℤ l))         ≡⟨ +HomScalar (pos (ℕ.suc ℕ.zero)) (pos (ℕ.suc n) +ℤ l) ⟩
    scalar 1 + scalar (pos (ℕ.suc n) +ℤ l)     ≡⟨ refl ⟩
    1r + (scalar (pos (ℕ.suc n) +ℤ l))         ≡[ i ]⟨ 1r + +HomScalar (pos (ℕ.suc n)) l i ⟩
    1r + (scalar (pos (ℕ.suc n)) + scalar l)   ≡⟨ +Assoc _ _ _ ⟩
    (1r + scalar (pos (ℕ.suc n))) + scalar l   ≡⟨ refl ⟩
    scalar (pos (ℕ.suc (ℕ.suc n))) + scalar l ∎

  +HomScalar (negsuc n) l = {!!}

AlmostRing→RawℤAlgebra : CommRing {ℓ} → RawAlgebra ℤAsRawRing ℓ
AlmostRing→RawℤAlgebra (R , commringstr 0r 1r _+_ _·_ -_ isCommRing) =
  rawalgebra R (scalar ((R , commringstr 0r 1r _+_ _·_ -_ isCommRing))) 0r 1r _+_ _·_ -_

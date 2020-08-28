{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.Ring.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Foundations.SIP

open import Cubical.Data.Sigma

open import Cubical.Structures.Axioms
open import Cubical.Structures.Auto
open import Cubical.Structures.Macro
open import Cubical.Algebra.Semigroup    hiding (⟨_⟩)
open import Cubical.Algebra.Monoid       hiding (⟨_⟩)
open import Cubical.Algebra.AbGroup   hiding (⟨_⟩)
open import Cubical.Algebra.Ring.Base

private
  variable
    ℓ : Level

{-
  some basic calculations (used for example in QuotientRing.agda),
  that should become obsolete or subject to change once we have a
  ring solver (see https://github.com/agda/cubical/issues/297)
-}
module Theory (R' : Ring {ℓ}) where

  open Ring R' renaming ( Carrier to R )

  implicitInverse : (x y : R)
                 → x + y ≡ 0r
                 → y ≡ - x
  implicitInverse x y p =
    y               ≡⟨ sym (+-lid y) ⟩
    0r + y          ≡⟨ cong (λ u → u + y) (sym (+-linv x)) ⟩
    (- x + x) + y   ≡⟨ sym (+-assoc _ _ _) ⟩
    (- x) + (x + y) ≡⟨ cong (λ u → (- x) + u) p ⟩
    (- x) + 0r      ≡⟨ +-rid _ ⟩
    - x             ∎

  0-selfinverse : - 0r ≡ 0r
  0-selfinverse = sym (implicitInverse _ _ (+-rid 0r))

  0-idempotent : 0r + 0r ≡ 0r
  0-idempotent = +-lid 0r

  +-idempotency→0 : (x : R) → x ≡ x + x → 0r ≡ x
  +-idempotency→0 x p =
    0r              ≡⟨ sym (+-rinv _) ⟩
    x + (- x)       ≡⟨ cong (λ u → u + (- x)) p ⟩
    (x + x) + (- x) ≡⟨ sym (+-assoc _ _ _) ⟩
    x + (x + (- x)) ≡⟨ cong (λ u → x + u) (+-rinv _) ⟩
    x + 0r          ≡⟨ +-rid x ⟩
    x               ∎

  0-rightNullifies : (x : R) → x · 0r ≡ 0r
  0-rightNullifies x =
              let x·0-is-idempotent : x · 0r ≡ x · 0r + x · 0r
                  x·0-is-idempotent =
                    x · 0r               ≡⟨ cong (λ u → x · u) (sym 0-idempotent) ⟩
                    x · (0r + 0r)        ≡⟨ ·-rdist-+ _ _ _ ⟩
                    (x · 0r) + (x · 0r)  ∎
              in sym (+-idempotency→0 _ x·0-is-idempotent)

  0-leftNullifies : (x : R) → 0r · x ≡ 0r
  0-leftNullifies x =
              let 0·x-is-idempotent : 0r · x ≡ 0r · x + 0r · x
                  0·x-is-idempotent =
                    0r · x               ≡⟨ cong (λ u → u · x) (sym 0-idempotent) ⟩
                    (0r + 0r) · x        ≡⟨ ·-ldist-+ _ _ _ ⟩
                    (0r · x) + (0r · x)  ∎
              in sym (+-idempotency→0 _ 0·x-is-idempotent)

  -commutesWithRight-· : (x y : R) →  x · (- y) ≡ - (x · y)
  -commutesWithRight-· x y = implicitInverse (x · y) (x · (- y))

                               (x · y + x · (- y)     ≡⟨ sym (·-rdist-+ _ _ _) ⟩
                               x · (y + (- y))        ≡⟨ cong (λ u → x · u) (+-rinv y) ⟩
                               x · 0r                 ≡⟨ 0-rightNullifies x ⟩
                               0r ∎)

  -commutesWithLeft-· : (x y : R) →  (- x) · y ≡ - (x · y)
  -commutesWithLeft-· x y = implicitInverse (x · y) ((- x) · y)

                              (x · y + (- x) · y     ≡⟨ sym (·-ldist-+ _ _ _) ⟩
                              (x - x) · y            ≡⟨ cong (λ u → u · y) (+-rinv x) ⟩
                              0r · y                 ≡⟨ 0-leftNullifies y ⟩
                              0r ∎)

  -isDistributive : (x y : R) → (- x) + (- y) ≡ - (x + y)
  -isDistributive x y =
    implicitInverse _ _
         ((x + y) + ((- x) + (- y)) ≡⟨ sym (+-assoc _ _ _) ⟩
          x + (y + ((- x) + (- y))) ≡⟨ cong
                                         (λ u → x + (y + u))
                                         (+-comm _ _) ⟩
          x + (y + ((- y) + (- x))) ≡⟨ cong (λ u → x + u) (+-assoc _ _ _) ⟩
          x + ((y + (- y)) + (- x)) ≡⟨ cong (λ u → x + (u + (- x)))
                                            (+-rinv _) ⟩
          x + (0r + (- x))           ≡⟨ cong (λ u → x + u) (+-lid _) ⟩
          x + (- x)                 ≡⟨ +-rinv _ ⟩
          0r ∎)

  translatedDifference : (x a b : R) → a - b ≡ (x + a) - (x + b)
  translatedDifference x a b =
              a - b                       ≡⟨ cong (λ u → a + u)
                                                  (sym (+-lid _)) ⟩
              (a + (0r + (- b)))          ≡⟨ cong (λ u → a + (u + (- b)))
                                                  (sym (+-rinv _)) ⟩
              (a + ((x + (- x)) + (- b))) ≡⟨ cong (λ u → a + u)
                                                  (sym (+-assoc _ _ _)) ⟩
              (a + (x + ((- x) + (- b)))) ≡⟨ (+-assoc _ _ _) ⟩
              ((a + x) + ((- x) + (- b))) ≡⟨ cong (λ u → u + ((- x) + (- b)))
                                                  (+-comm _ _) ⟩
              ((x + a) + ((- x) + (- b))) ≡⟨ cong (λ u → (x + a) + u)
                                                  (-isDistributive _ _) ⟩
              ((x + a) - (x + b)) ∎

  +-assoc-comm1 : (x y z : R) → x + (y + z) ≡ y + (x + z)
  +-assoc-comm1 x y z = +-assoc x y z ∙∙ cong (λ x → x + z) (+-comm x y) ∙∙ sym (+-assoc y x z)

  +-assoc-comm2 : (x y z : R) → x + (y + z) ≡ z + (y + x)
  +-assoc-comm2 x y z = +-assoc-comm1 x y z ∙∙ cong (λ x → y + x) (+-comm x z) ∙∙ +-assoc-comm1 y z x

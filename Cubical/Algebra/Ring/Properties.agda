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
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.AbGroup
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

  open RingStr (snd R')
  private R = ⟨ R' ⟩
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

  equalByDifference : (x y : R)
                      → x - y ≡ 0r
                      → x ≡ y
  equalByDifference x y p =
    x               ≡⟨ sym (+-rid _) ⟩
    x + 0r          ≡⟨ cong (λ u → x + u) (sym (+-linv y)) ⟩
    x + ((- y) + y) ≡⟨ +-assoc _ _ _ ⟩
    (x - y) + y     ≡⟨ cong (λ u → u + y) p ⟩
    0r + y          ≡⟨ +-lid _ ⟩
    y               ∎

  0-selfinverse : - 0r ≡ 0r
  0-selfinverse = sym (implicitInverse _ _ (+-rid 0r))

  0-idempotent : 0r + 0r ≡ 0r
  0-idempotent = +-lid 0r

  +-idempotency→0 : (x : R) → x ≡ x + x → x ≡ 0r
  +-idempotency→0 x p =
    x               ≡⟨ sym (+-rid x) ⟩
    x + 0r          ≡⟨ cong (λ u → x + u) (sym (+-rinv _)) ⟩
    x + (x + (- x)) ≡⟨ +-assoc _ _ _ ⟩
    (x + x) + (- x) ≡⟨ cong (λ u → u + (- x)) (sym p) ⟩
    x + (- x)       ≡⟨ +-rinv _ ⟩
    0r              ∎

  0-rightNullifies : (x : R) → x · 0r ≡ 0r
  0-rightNullifies x =
              let x·0-is-idempotent : x · 0r ≡ x · 0r + x · 0r
                  x·0-is-idempotent =
                    x · 0r               ≡⟨ cong (λ u → x · u) (sym 0-idempotent) ⟩
                    x · (0r + 0r)        ≡⟨ ·-rdist-+ _ _ _ ⟩
                    (x · 0r) + (x · 0r)  ∎
              in (+-idempotency→0 _ x·0-is-idempotent)

  0-leftNullifies : (x : R) → 0r · x ≡ 0r
  0-leftNullifies x =
              let 0·x-is-idempotent : 0r · x ≡ 0r · x + 0r · x
                  0·x-is-idempotent =
                    0r · x               ≡⟨ cong (λ u → u · x) (sym 0-idempotent) ⟩
                    (0r + 0r) · x        ≡⟨ ·-ldist-+ _ _ _ ⟩
                    (0r · x) + (0r · x)  ∎
              in +-idempotency→0 _ 0·x-is-idempotent

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

  ·-assoc2 : (x y z w : R) → (x · y) · (z · w) ≡ x · (y · z) · w
  ·-assoc2 x y z w = ·-assoc (x · y) z w ∙ cong (_· w) (sym (·-assoc x y z))

module HomTheory {R S : Ring {ℓ}} (f′ : RingHom  R S) where
  open Theory ⦃...⦄
  open RingStr ⦃...⦄
  open RingHom f′
  private
    instance
      _ = R
      _ = S
      _ = snd R
      _ = snd S

  homPres0 : f 0r ≡ 0r
  homPres0 = +-idempotency→0 (f 0r)
               (f 0r        ≡⟨ sym (cong f 0-idempotent) ⟩
                f (0r + 0r) ≡⟨ isHom+ _ _ ⟩
                f 0r + f 0r ∎)

  -commutesWithHom : (x : ⟨ R ⟩) → f (- x) ≡ - (f x)
  -commutesWithHom x = implicitInverse _ _
                         (f x + f (- x)   ≡⟨ sym (isHom+ _ _) ⟩
                          f (x + (- x))   ≡⟨ cong f (+-rinv x) ⟩
                          f 0r            ≡⟨ homPres0 ⟩
                          0r ∎)

  ker≡0→inj : ({x : ⟨ R ⟩} → f x ≡ 0r → x ≡ 0r)
            → ({x y : ⟨ R ⟩} → f x ≡ f y → x ≡ y)
  ker≡0→inj ker≡0 {x} {y} p = equalByDifference _ _ (ker≡0 path)
   where
   path : f (x - y) ≡ 0r
   path = f (x - y)     ≡⟨ isHom+ _ _ ⟩
          f x + f (- y) ≡⟨ cong (f x +_) (-commutesWithHom _) ⟩
          f x - f y     ≡⟨ cong (_- f y) p ⟩
          f y - f y     ≡⟨ +-rinv _ ⟩
          0r            ∎


module _{R S : Ring {ℓ}} (φ ψ : RingHom  R S) where
 open RingStr ⦃...⦄
 open RingHom
 private
   instance
     _ = R
     _ = S
     _ = snd R
     _ = snd S

 RingHom≡f : f φ ≡ f ψ → φ ≡ ψ
 f (RingHom≡f p i) = p i
 pres1 (RingHom≡f p i) = isProp→PathP {B = λ i → p i 1r ≡ 1r}
                                      (λ _ → is-set _ _) (pres1 φ) (pres1 ψ) i
 isHom+ (RingHom≡f p i) = isProp→PathP {B = λ i → ∀ x y → p i (x + y) ≡ (p i x) + (p i y) }
                                      (λ _ → isPropΠ2 (λ _ _ → is-set _ _)) (isHom+ φ) (isHom+ ψ) i
 isHom· (RingHom≡f p i) = isProp→PathP {B = λ i → ∀ x y → p i (x · y) ≡ (p i x) · (p i y) }
                                      (λ _ → isPropΠ2 (λ _ _ → is-set _ _)) (isHom· φ) (isHom· ψ) i


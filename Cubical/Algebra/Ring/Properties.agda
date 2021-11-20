{-# OPTIONS --safe #-}
module Cubical.Algebra.Ring.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
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
module RingTheory (R' : Ring ℓ) where

  open RingStr (snd R')
  private R = ⟨ R' ⟩
  implicitInverse : (x y : R)
                 → x + y ≡ 0r
                 → y ≡ - x
  implicitInverse x y p =
    y               ≡⟨ sym (+Lid y) ⟩
    0r + y          ≡⟨ cong (λ u → u + y) (sym (+Linv x)) ⟩
    (- x + x) + y   ≡⟨ sym (+Assoc _ _ _) ⟩
    (- x) + (x + y) ≡⟨ cong (λ u → (- x) + u) p ⟩
    (- x) + 0r      ≡⟨ +Rid _ ⟩
    - x             ∎

  equalByDifference : (x y : R)
                      → x - y ≡ 0r
                      → x ≡ y
  equalByDifference x y p =
    x               ≡⟨ sym (+Rid _) ⟩
    x + 0r          ≡⟨ cong (λ u → x + u) (sym (+Linv y)) ⟩
    x + ((- y) + y) ≡⟨ +Assoc _ _ _ ⟩
    (x - y) + y     ≡⟨ cong (λ u → u + y) p ⟩
    0r + y          ≡⟨ +Lid _ ⟩
    y               ∎

  0Selfinverse : - 0r ≡ 0r
  0Selfinverse = sym (implicitInverse _ _ (+Rid 0r))

  0Idempotent : 0r + 0r ≡ 0r
  0Idempotent = +Lid 0r

  +Idempotency→0 : (x : R) → x ≡ x + x → x ≡ 0r
  +Idempotency→0 x p =
    x               ≡⟨ sym (+Rid x) ⟩
    x + 0r          ≡⟨ cong (λ u → x + u) (sym (+Rinv _)) ⟩
    x + (x + (- x)) ≡⟨ +Assoc _ _ _ ⟩
    (x + x) + (- x) ≡⟨ cong (λ u → u + (- x)) (sym p) ⟩
    x + (- x)       ≡⟨ +Rinv _ ⟩
    0r              ∎

  -Idempotent : (x : R) → -(- x) ≡ x
  -Idempotent x =  - (- x)   ≡⟨ sym (implicitInverse (- x) x (+Linv _)) ⟩
                   x ∎

  0RightAnnihilates : (x : R) → x · 0r ≡ 0r
  0RightAnnihilates x =
              let x·0-is-idempotent : x · 0r ≡ x · 0r + x · 0r
                  x·0-is-idempotent =
                    x · 0r               ≡⟨ cong (λ u → x · u) (sym 0Idempotent) ⟩
                    x · (0r + 0r)        ≡⟨ ·Rdist+ _ _ _ ⟩
                    (x · 0r) + (x · 0r)  ∎
              in (+Idempotency→0 _ x·0-is-idempotent)

  0LeftAnnihilates : (x : R) → 0r · x ≡ 0r
  0LeftAnnihilates x =
              let 0·x-is-idempotent : 0r · x ≡ 0r · x + 0r · x
                  0·x-is-idempotent =
                    0r · x               ≡⟨ cong (λ u → u · x) (sym 0Idempotent) ⟩
                    (0r + 0r) · x        ≡⟨ ·Ldist+ _ _ _ ⟩
                    (0r · x) + (0r · x)  ∎
              in +Idempotency→0 _ 0·x-is-idempotent

  -DistR· : (x y : R) →  x · (- y) ≡ - (x · y)
  -DistR· x y = implicitInverse (x · y) (x · (- y))

                               (x · y + x · (- y)     ≡⟨ sym (·Rdist+ _ _ _) ⟩
                               x · (y + (- y))        ≡⟨ cong (λ u → x · u) (+Rinv y) ⟩
                               x · 0r                 ≡⟨ 0RightAnnihilates x ⟩
                               0r ∎)

  -DistL· : (x y : R) →  (- x) · y ≡ - (x · y)
  -DistL· x y = implicitInverse (x · y) ((- x) · y)

                              (x · y + (- x) · y     ≡⟨ sym (·Ldist+ _ _ _) ⟩
                              (x - x) · y            ≡⟨ cong (λ u → u · y) (+Rinv x) ⟩
                              0r · y                 ≡⟨ 0LeftAnnihilates y ⟩
                              0r ∎)

  -Swap· : (x y : R) → (- x) · y ≡ x · (- y)
  -Swap· _ _ = -DistL· _ _ ∙ sym (-DistR· _ _)

  -IsMult-1 : (x : R) → - x ≡ (- 1r) · x
  -IsMult-1 _ = sym (·Lid _) ∙ sym (-Swap· _ _)

  -Dist : (x y : R) → (- x) + (- y) ≡ - (x + y)
  -Dist x y =
    implicitInverse _ _
         ((x + y) + ((- x) + (- y)) ≡⟨ sym (+Assoc _ _ _) ⟩
          x + (y + ((- x) + (- y))) ≡⟨ cong
                                         (λ u → x + (y + u))
                                         (+Comm _ _) ⟩
          x + (y + ((- y) + (- x))) ≡⟨ cong (λ u → x + u) (+Assoc _ _ _) ⟩
          x + ((y + (- y)) + (- x)) ≡⟨ cong (λ u → x + (u + (- x)))
                                            (+Rinv _) ⟩
          x + (0r + (- x))           ≡⟨ cong (λ u → x + u) (+Lid _) ⟩
          x + (- x)                 ≡⟨ +Rinv _ ⟩
          0r ∎)

  translatedDifference : (x a b : R) → a - b ≡ (x + a) - (x + b)
  translatedDifference x a b =
              a - b                       ≡⟨ cong (λ u → a + u)
                                                  (sym (+Lid _)) ⟩
              (a + (0r + (- b)))          ≡⟨ cong (λ u → a + (u + (- b)))
                                                  (sym (+Rinv _)) ⟩
              (a + ((x + (- x)) + (- b))) ≡⟨ cong (λ u → a + u)
                                                  (sym (+Assoc _ _ _)) ⟩
              (a + (x + ((- x) + (- b)))) ≡⟨ (+Assoc _ _ _) ⟩
              ((a + x) + ((- x) + (- b))) ≡⟨ cong (λ u → u + ((- x) + (- b)))
                                                  (+Comm _ _) ⟩
              ((x + a) + ((- x) + (- b))) ≡⟨ cong (λ u → (x + a) + u)
                                                  (-Dist _ _) ⟩
              ((x + a) - (x + b)) ∎

  +Assoc-comm1 : (x y z : R) → x + (y + z) ≡ y + (x + z)
  +Assoc-comm1 x y z = +Assoc x y z ∙∙ cong (λ x → x + z) (+Comm x y) ∙∙ sym (+Assoc y x z)

  +Assoc-comm2 : (x y z : R) → x + (y + z) ≡ z + (y + x)
  +Assoc-comm2 x y z = +Assoc-comm1 x y z ∙∙ cong (λ x → y + x) (+Comm x z) ∙∙ +Assoc-comm1 y z x

  +ShufflePairs : (a b c d : R)
                → (a + b) + (c + d) ≡ (a + c) + (b + d)
  +ShufflePairs a b c d =
    (a + b) + (c + d) ≡⟨ +Assoc _ _ _ ⟩
    ((a + b) + c) + d ≡⟨ cong (λ u → u + d) (sym (+Assoc _ _ _)) ⟩
    (a + (b + c)) + d ≡⟨ cong (λ u → (a + u) + d) (+Comm _ _) ⟩
    (a + (c + b)) + d ≡⟨ cong (λ u → u + d) (+Assoc _ _ _) ⟩
    ((a + c) + b) + d ≡⟨ sym (+Assoc _ _ _) ⟩
    (a + c) + (b + d) ∎

  ·-assoc2 : (x y z w : R) → (x · y) · (z · w) ≡ x · (y · z) · w
  ·-assoc2 x y z w = ·Assoc (x · y) z w ∙ cong (_· w) (sym (·Assoc x y z))


module RingHoms where
  open IsRingHom

  idRingHom : (R : Ring ℓ) → RingHom R R
  fst (idRingHom R) = idfun (fst R)
  snd (idRingHom R) = makeIsRingHom refl (λ _ _ → refl) (λ _ _ → refl)

  compRingHom : {R S T : Ring ℓ} → RingHom R S → RingHom S T → RingHom R T
  fst (compRingHom f g) x = g .fst (f .fst x)
  snd (compRingHom f g) = makeIsRingHom (cong (g .fst) (pres1 (snd f)) ∙ pres1 (snd g))
                                        (λ x y → cong (g .fst) (pres+ (snd f) _ _) ∙ pres+ (snd g) _ _)
                                        (λ x y → cong (g .fst) (pres· (snd f) _ _) ∙ pres· (snd g) _ _)

  compIdRingHom : {R S : Ring ℓ} (φ : RingHom R S) → compRingHom (idRingHom R) φ ≡ φ
  compIdRingHom φ = RingHom≡ refl

  idCompRingHom : {R S : Ring ℓ} (φ : RingHom R S) → compRingHom φ (idRingHom S) ≡ φ
  idCompRingHom φ = RingHom≡ refl

  compAssocRingHom : {R S T U : Ring ℓ} (φ : RingHom R S) (ψ : RingHom S T) (χ : RingHom T U) →
                     compRingHom (compRingHom φ ψ) χ ≡ compRingHom φ (compRingHom ψ χ)
  compAssocRingHom _ _ _ = RingHom≡ refl


module RingHomTheory {R S : Ring ℓ} (φ : RingHom R S) where
  open RingTheory ⦃...⦄
  open RingStr ⦃...⦄
  open IsRingHom (φ .snd)
  private
    instance
      _ = R
      _ = S
      _ = snd R
      _ = snd S
    f = fst φ

  ker≡0→inj : ({x : ⟨ R ⟩} → f x ≡ 0r → x ≡ 0r)
            → ({x y : ⟨ R ⟩} → f x ≡ f y → x ≡ y)
  ker≡0→inj ker≡0 {x} {y} p = equalByDifference _ _ (ker≡0 path)
   where
   path : f (x - y) ≡ 0r
   path = f (x - y)     ≡⟨ pres+ _ _ ⟩
          f x + f (- y) ≡⟨ cong (f x +_) (pres- _) ⟩
          f x - f y     ≡⟨ cong (_- f y) p ⟩
          f y - f y     ≡⟨ +Rinv _ ⟩
          0r            ∎

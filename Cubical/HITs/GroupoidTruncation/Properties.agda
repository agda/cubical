{-

This file contains:

- Properties of groupoid truncations

-}
{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.GroupoidTruncation.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.HITs.GroupoidTruncation.Base

recGroupoidTrunc : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (gB : isGroupoid B) → (A → B) → (∥ A ∥₁ → B)
recGroupoidTrunc gB f ∣ x ∣₁ = f x
recGroupoidTrunc gB f (squash₁ _ _ _ _ r s i j k) =
  gB _ _ _ _
    (λ m n → recGroupoidTrunc gB f (r m n))
    (λ m n → recGroupoidTrunc gB f (s m n))
    i j k

groupoidTruncFib : ∀ {ℓ ℓ'} {A : Type ℓ} (P : A → Type ℓ')
              {a b : A} (sPb : isGroupoid (P b))
              {p q : a ≡ b} {r s : p ≡ q} (u : r ≡ s) {a1 : P a} {b1 : P b}
              {p1 : PathP (λ i → P (p i)) a1 b1}
              {q1 : PathP (λ i → P (q i)) a1 b1}
              (r1 : PathP (λ i → PathP (λ j → P (r i j)) a1 b1) p1 q1)
              (s1 : PathP (λ i → PathP (λ j → P (s i j)) a1 b1) p1 q1)
            → PathP (λ i → PathP (λ j → PathP (λ k → P (u i j k)) a1 b1) p1 q1) r1 s1
groupoidTruncFib P {a} {b} sPb u {a1} {b1} {p1} {q1} r1 s1 i j k =
  hcomp (λ l → λ { (i = i0) → r1 j k
                 ; (i = i1) → s1 j k
                 ; (j = i0) → p1 k
                 ; (j = i1) → q1 k
                 ; (k = i0) → a1
                 ; (k = i1) → sPb b1 b1 refl refl (λ i j → Lb i j i1) refl l i j
                 })
        (Lb i j k)
  where
  L : (i j : I) → P b
  L i j = comp (λ k → P (u i j k)) _
               (λ k → λ { (i = i0) → r1 j k
                        ; (i = i1) → s1 j k
                        ; (j = i0) → p1 k
                        ; (j = i1) → q1 k })
               a1
  Lb : PathP (λ i → PathP (λ j → PathP (λ k → P (u i j k)) a1 (L i j)) p1 q1) r1 s1
  Lb i j k = fill (λ k → P (u i j k))
                  (λ k → λ { (i = i0) → r1 j k
                           ; (i = i1) → s1 j k
                           ; (j = i0) → p1 k
                           ; (j = i1) → q1 k })
                  (inS a1) k

groupoidTruncElim : ∀ {ℓ ℓ'} (A : Type ℓ) (B : ∥ A ∥₁ → Type ℓ')
                    (bG : (x : ∥ A ∥₁) → isGroupoid (B x))
                    (f : (x : A) → B ∣ x ∣₁) (x : ∥ A ∥₁) → B x
groupoidTruncElim A B bG f (∣ x ∣₁) = f x
groupoidTruncElim A B bG f (squash₁ x y p q r s i j k) =
  groupoidTruncFib B (bG y)
                   (squash₁ x y p q r s)
                   (λ i j → groupoidTruncElim A B bG f (r i j))
                   (λ i j → groupoidTruncElim A B bG f (s i j))
                   i j k

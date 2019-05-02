{-

This file contains:

- Properties of 2-groupoid truncations

-}
{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.2GroupoidTruncation.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.HITs.2GroupoidTruncation.Base

rec2GroupoidTrunc : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (gB : is2Groupoid B) → (A → B) → (∥ A ∥₂ → B)
rec2GroupoidTrunc gB f ∣ x ∣₂ = f x
rec2GroupoidTrunc gB f (squash₂ _ _ _ _ _ _ t u i j k l) =
  gB _ _ _ _ _ _
    (λ m n o → rec2GroupoidTrunc gB f (t m n o))
    (λ m n o → rec2GroupoidTrunc gB f (u m n o))
    i j k l

g2TruncFib : ∀ {ℓ ℓ'} {A : Type ℓ} (P : A → Type ℓ')
             {a b : A} (sPb : is2Groupoid (P b))
             {p q : a ≡ b} {r s : p ≡ q} {u v : r ≡ s} (w : u ≡ v) {a1 : P a} {b1 : P b}
             {p1 : PathP (λ i → P (p i)) a1 b1}
             {q1 : PathP (λ i → P (q i)) a1 b1}
             {r1 : PathP (λ i → PathP (λ j → P (r i j)) a1 b1) p1 q1}
             {s1 : PathP (λ i → PathP (λ j → P (s i j)) a1 b1) p1 q1}
             (u1 : PathP (λ i → PathP (λ j → PathP (λ k → P (u i j k)) a1 b1) p1 q1) r1 s1)
             (v1 : PathP (λ i → PathP (λ j → PathP (λ k → P (v i j k)) a1 b1) p1 q1) r1 s1)
           → PathP (λ i → PathP (λ j → PathP (λ k → PathP (λ l → P (w i j k l)) a1 b1) p1 q1) r1 s1) u1 v1
g2TruncFib {A} P {a} {b} sPb {p} {q} {r} {s} {u} {v} w
           {a1} {b1} {p1} {q1} {r1} {s1} u1 v1 i j k l
  = hcomp (λ m → λ { (i = i0) → u1 j k l
                   ; (i = i1) → v1 j k l
                   ; (j = i0) → r1 k l
                   ; (j = i1) → s1 k l
                   ; (k = i0) → p1 l
                   ; (k = i1) → q1 l
                   ; (l = i0) → a1
                   ; (l = i1) → sPb b1 b1 refl refl refl refl L refl m i j k
                   })
          (Lb i j k l)
  where
  L : Path (Path (b1 ≡ b1) refl refl) refl refl
  L i j k = comp (λ l → P (w i j k l)) _
                 (λ l → λ { (i = i0) → u1 j k l
                          ; (i = i1) → v1 j k l
                          ; (j = i0) → r1 k l
                          ; (j = i1) → s1 k l
                          ; (k = i0) → p1 l
                          ; (k = i1) → q1 l
                          })
                 a1
  Lb : PathP (λ i → PathP (λ j → PathP (λ k → PathP (λ l → P (w i j k l)) a1 (L i j k)) p1 q1) r1 s1) u1 v1
  Lb i j k l = fill (λ l → P (w i j k l))
                    (λ l → λ { (i = i0) → u1 j k l
                             ; (i = i1) → v1 j k l
                             ; (j = i0) → r1 k l
                             ; (j = i1) → s1 k l
                             ; (k = i0) → p1 l
                             ; (k = i1) → q1 l
                             })
                    (inS a1) l

g2TruncElim : ∀ {ℓ ℓ'} (A : Type ℓ) (B : ∥ A ∥₂ → Type ℓ')
                    (bG : (x : ∥ A ∥₂) → is2Groupoid (B x))
                    (f : (x : A) → B ∣ x ∣₂) (x : ∥ A ∥₂) → B x
g2TruncElim A B bG f ∣ x ∣₂ = f x
g2TruncElim A B bG f (squash₂ x y p q r s u v i j k l) =
  g2TruncFib {A = ∥ A ∥₂} B {x} {y} (bG y) {p} {q} {r} {s} {u} {v}
               (squash₂ x y p q r s u v)
               {g2TruncElim A B bG f x}
               {g2TruncElim A B bG f y}
               {λ i → g2TruncElim A B bG f (p i)}
               {λ i → g2TruncElim A B bG f (q i)}
               {λ i j → g2TruncElim A B bG f (r i j)}
               {λ i j → g2TruncElim A B bG f (s i j)}
               (λ i j k → g2TruncElim A B bG f (u i j k))
               (λ i j k → g2TruncElim A B bG f (v i j k))
               i j k l

{-

Proof that any isomorphism is an equivalence.

-}
{-# OPTIONS --cubical #-}
module Cubical.Basics.IsoToEquiv where

open import Cubical.Core.Primitives
open import Cubical.Core.Prelude
open import Cubical.Core.Glue

module _ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) (g : B → A)
         (s : (y : B) → f (g y) ≡ y) (t : (x : A) → g (f x) ≡ x) where

  private
    module _ (y : B) (x0 x1 : A) (p0 : y ≡ f x0) (p1 : y ≡ f x1) where
      fill0 : I → I → A
      fill0 i = hfill (λ k → λ { (i = i1) → t x0 k; (i = i0) → g y })
                      (inc (g (p0 i)))

      fill1 : I → I → A
      fill1 i = hfill (λ k → λ { (i = i1) → t x1 k; (i = i0) → g y })
                      (inc (g (p1 i)))

      fill2 : I → I → A
      fill2 i = hfill (λ k → λ { (i = i1) → fill1 k i1; (i = i0) → fill0 k i1 })
                      (inc (g y))

      p : x0 ≡ x1
      p i = fill2 i i1

      sq : I → I → A
      sq i j = hcomp (λ k → λ { (i = i1) → fill1 j (~ k)
                              ; (i = i0) → fill0 j (~ k)
                              ; (j = i1) → t (fill2 i i1) (~ k)
                              ; (j = i0) → g y })
                     (fill2 i j)

      sq1 : I → I → B
      sq1 i j = hcomp (λ k → λ { (i = i1) → s (p1 j) k
                               ; (i = i0) → s (p0 j) k
                               ; (j = i1) → s (f (p i)) k
                               ; (j = i0) → s y k })
                      (f (sq i j))

      lemIso : (x0 , p0) ≡ (x1 , p1)
      lemIso i .fst = p i
      lemIso i .snd = λ j → sq1 i j

  isoToIsEquiv : isEquiv f
  isoToIsEquiv .equiv-proof y .fst .fst = g y
  isoToIsEquiv .equiv-proof y .fst .snd = sym (s y)
  isoToIsEquiv .equiv-proof y .snd z = lemIso y (g y) (fst z) (sym (s y)) (snd z)

  isoToEquiv : A ≃ B
  isoToEquiv = _ , isoToIsEquiv

module _ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (w : A ≃ B) where
  invEq : (y : B) → A
  invEq y = fst (fst (snd w .equiv-proof y))

  secEq : (x : A) → invEq (fst w x) ≡ x
  secEq x = λ i → fst (snd (snd w .equiv-proof (fst w x)) (x , (λ j → fst w x)) i)

  retEq : (y : B) → fst w (invEq y) ≡ y
  retEq y = λ i → snd (fst (snd w .equiv-proof y)) (~ i)

isoToPath : ∀ {ℓ} {A B : Set ℓ} (f : A → B) (g : B → A)
  (s : (y : B) → f (g y) ≡ y) (t : (x : A) → g (f x) ≡ x) → A ≡ B
isoToPath f g s t = ua (isoToEquiv f g s t)

invEquiv : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → A ≃ B → B ≃ A
invEquiv f = isoToEquiv (invEq f) (fst f) (secEq f) (retEq f)

-- module _ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'}  where
--   invEquivInvol : (f : A ≃ B) → invEquiv (invEquiv f) ≡ f
--   invEquivInvol f i .fst = fst f
--   invEquivInvol f i .snd = propIsEquiv (fst f) (snd (invEquiv (invEquiv f))) (snd f) i

{-

Theory about isomorphisms

- Definitions of [section] and [retract]
- Definition of isomorphisms ([Iso])
- Any isomorphism is an equivalence ([isoToEquiv])

-}
{-# OPTIONS --cubical --safe #-}
module Cubical.Foundations.Isomorphism where

open import Cubical.Core.Everything
open import Cubical.Foundations.HLevels

-- Section and retract
module _ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} where
  section : (f : A → B) → (g : B → A) → Set ℓ'
  section f g = ∀ b → f (g b) ≡ b

  -- NB: `g` is the retraction!
  retract : (f : A → B) → (g : B → A) → Set ℓ
  retract f g = ∀ a → g (f a) ≡ a
  
record Iso {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') : Set (ℓ-max ℓ ℓ') where
  constructor iso
  field
    fun : A → B
    inv : B → A
    rightInv : section fun inv
    leftInv : retract fun inv

-- Any iso is an equivalence
module _ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (i : Iso A B) where
  open Iso i renaming ( fun to f
                      ; inv to g
                      ; rightInv to s
                      ; leftInv to t)
                                  
  private
    module _ (y : B) (x0 x1 : A) (p0 : f x0 ≡ y) (p1 : f x1 ≡ y) where
      fill0 : I → I → A
      fill0 i = hfill (λ k → λ { (i = i1) → t x0 k
                               ; (i = i0) → g y })
                      (inc (g (p0 (~ i))))

      fill1 : I → I → A
      fill1 i = hfill (λ k → λ { (i = i1) → t x1 k
                               ; (i = i0) → g y })
                      (inc (g (p1 (~ i))))

      fill2 : I → I → A
      fill2 i = hfill (λ k → λ { (i = i1) → fill1 k i1
                               ; (i = i0) → fill0 k i1 })
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
      sq1 i j = hcomp (λ k → λ { (i = i1) → s (p1 (~ j)) k
                               ; (i = i0) → s (p0 (~ j)) k
                               ; (j = i1) → s (f (p i)) k
                               ; (j = i0) → s y k })
                      (f (sq i j))

      lemIso : (x0 , p0) ≡ (x1 , p1)
      lemIso i .fst = p i
      lemIso i .snd = λ j → sq1 i (~ j)

  isoToIsEquiv : isEquiv f
  isoToIsEquiv .equiv-proof y .fst .fst = g y
  isoToIsEquiv .equiv-proof y .fst .snd = s y
  isoToIsEquiv .equiv-proof y .snd z = lemIso y (g y) (fst z) (s y) (snd z)


isoToPath : ∀ {ℓ} {A B : Set ℓ} → (Iso A B) → A ≡ B
isoToPath f = ua (Iso.fun f , isoToIsEquiv f)


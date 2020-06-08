{-

Half adjoint equivalences ([HAEquiv])

- Iso to HAEquiv ([iso→HAEquiv])
- Equiv to HAEquiv ([equiv→HAEquiv])
- Cong is an equivalence ([congEquiv])

-}
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Foundations.Equiv.HalfAdjoint where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.GroupoidLaws

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    B : Type ℓ'

record isHAEquiv {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B) : Type (ℓ-max ℓ ℓ') where
  field
    g : B → A
    sec : ∀ a → g (f a) ≡ a
    ret : ∀ b → f (g b) ≡ b
    com : ∀ a → cong f (sec a) ≡ ret (f a)

  -- from redtt's ha-equiv/symm
  com-op : ∀ b → cong g (ret b) ≡ sec (g b)
  com-op b j i = hcomp (λ k → λ { (i = i0) → sec (g b) (j ∧ (~ k))
                                ; (j = i0) → g (ret b i)
                                ; (j = i1) → sec (g b) (i ∨ (~ k))
                                ; (i = i1) → g b })
                       (cap1 j i)

    where cap0 : Square {- (j = i0) -} (λ i → f (g (ret b i)))
                        {- (j = i1) -} (λ i → ret b i)
                        {- (i = i0) -} (λ j → f (sec (g b) j))
                        {- (i = i1) -} (λ j → ret b j)

          cap0 j i = hcomp (λ k → λ { (i = i0) → com (g b) (~ k) j
                                    ; (j = i0) → f (g (ret b i))
                                    ; (j = i1) → ret b i
                                    ; (i = i1) → ret b j })
                           (ret (ret b i) j)

          filler : I → I → A
          filler j i = hfill (λ k → λ { (i = i0) → g (ret b k)
                                      ; (i = i1) → g b })
                             (inS (sec (g b) i)) j

          cap1 : Square {- (j = i0) -} (λ i → g (ret b i))
                        {- (j = i1) -} (λ i → g b)
                        {- (i = i0) -} (λ j → sec (g b) j)
                        {- (i = i1) -} (λ j → g b)

          cap1 j i = hcomp (λ k → λ { (i = i0) → sec (sec (g b) j) k
                                    ; (j = i0) → sec (g (ret b i)) k
                                    ; (j = i1) → filler i k
                                    ; (i = i1) → filler j k })
                           (g (cap0 j i))


HAEquiv : (A : Type ℓ) (B : Type ℓ') → Type (ℓ-max ℓ ℓ')
HAEquiv A B = Σ[ f ∈ (A → B) ] isHAEquiv f

-- vogt's lemma (https://ncatlab.org/nlab/show/homotopy+equivalence#vogts_lemma)
iso→HAEquiv : Iso A B → HAEquiv A B
iso→HAEquiv (iso f g ε η) = f , isHAEquivf
  where
    isHAEquivf : isHAEquiv f
    isHAEquiv.g isHAEquivf         = g
    isHAEquiv.sec isHAEquivf       = η
    isHAEquiv.ret isHAEquivf b i   =
      hcomp (λ j → λ { (i = i0) → ε (f (g b)) j
                     ; (i = i1) → ε b j })
            (f (η (g b) i))
    isHAEquiv.com isHAEquivf a i j =
      hcomp (λ k → λ { (i = i0) → ε (f (η a j)) k
                     ; (j = i0) → ε (f (g (f a))) k
                     ; (j = i1) → ε (f a) k})
            (f (Hfa≡fHa (λ x → g (f x)) η a (~ i) j))

equiv→HAEquiv : A ≃ B → HAEquiv A B
equiv→HAEquiv e = iso→HAEquiv (equivToIso e)

congIso : {x y : A} (e : A ≃ B) → Iso (x ≡ y) (e .fst x ≡ e .fst y)
congIso {x = x} {y} e = goal
  where
  open isHAEquiv (equiv→HAEquiv e .snd)
  open Iso

  goal : Iso (x ≡ y) (e .fst x ≡ e .fst y)
  fun goal   = cong (equiv→HAEquiv e .fst)
  inv goal p = sym (sec x) ∙∙ cong g p ∙∙ sec y
  rightInv goal p i j =
    hcomp (λ k → λ { (i = i0) → equiv→HAEquiv e .fst
                                  (doubleCompPath-filler (sym (sec x)) (cong g p) (sec y) k j)
                   ; (i = i1) → ret (p j) k
                   ; (j = i0) → com x i k
                   ; (j = i1) → com y i k })
          (equiv→HAEquiv e .fst (g (p j)))
  leftInv goal p i j =
    hcomp (λ k → λ { (i = i1) → p j
                   ; (j = i0) → secEq e x (i ∨ k)
                   ; (j = i1) → secEq e y (i ∨ k) })
          (secEq e (p j) i)

-- This is proved more directly in Foundations.Equiv.Properties, but
-- that proof is not as universe polymorphic as this one
isEquivCong : {x y : A} (e : A ≃ B) → isEquiv (λ (p : x ≡ y) → cong (e .fst) p)
isEquivCong e = isoToIsEquiv (congIso e)

congEquiv : {x y : A} (e : A ≃ B) → (x ≡ y) ≃ (e .fst x ≡ e .fst y)
congEquiv e = isoToEquiv (congIso e)

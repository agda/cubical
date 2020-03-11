{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.Pushout.Flattening where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

open import Cubical.Data.Sigma

open import Cubical.HITs.Pushout.Base

module FlatteningLemma {ℓa ℓb ℓc} {A : Type ℓa} {B : Type ℓb} {C : Type ℓc} (f : A → B) (g : A → C)
                       {ℓ} (F : B → Type ℓ) (G : C → Type ℓ) (e : ∀ a → F (f a) ≃ G (g a)) where

  E : Pushout f g → Type ℓ
  E (inl x) = F x
  E (inr x) = G x
  E (push a i) = ua (e a) i

  Σf : Σ[ a ∈ A ] F (f a) → Σ[ b ∈ B ] F b
  Σf (a , x) = (f a , x)

  Σg : Σ[ a ∈ A ] F (f a) → Σ[ c ∈ C ] G c
  Σg (a , x) = (g a , (e a) .fst x)

  module FlattenIso where

    fwd : Σ (Pushout f g) E → Pushout Σf Σg
    fwd (inl b , x) = inl (b , x)
    fwd (inr c , x) = inr (c , x)
    fwd (push a i , x) = hcomp (λ j → λ { (i = i0) → push (a , x) (~ j)
                                        ; (i = i1) → inr (g a , x) })
                               (inr (g a , unglue (i ∨ ~ i) x))

    bwd : Pushout Σf Σg → Σ (Pushout f g) E
    bwd (inl (b , x)) = (inl b , x)
    bwd (inr (c , x)) = (inr c , x)
    bwd (push (a , x) i) = (push a i , ua-gluePath (e a) {x = x} refl i)

    -- this case follows trivially due to the definitional equalities below
    fwd-bwd : ∀ x → fwd (bwd x) ≡ x
    fwd-bwd (inl (b , x)) = refl
    fwd-bwd (inr (c , x)) = refl
    fwd-bwd (push (a , x) i) j =
      hcomp (λ k → λ { (i = i0) → push (a , x) (~ k)       -- ua-gluePath (e a) {x = x} refl i0 := x
                     ; (i = i1) → inr (g a , (e a) .fst x) -- ua-gluePath (e a) {x = x} refl i1 := (e a) .fst x
                     ; (j = i1) → push (a , x) (i ∨ ~ k) })
            (inr (g a , (e a) .fst x)) -- unglue (i ∨ ~ i) (ua-gluePath (e a) {x = x} refl i) := (e a) .fst x

    sq : ∀ a → SquareP (λ i j → ua (e a) i → ua (e a) (i ∨ ~ j))
          {- i = i0 -} (λ j x → glue (λ { ((~ j) = i0) → x ; ((~ j) = i1) → (e a) .fst x }) ((e a) .fst x))
          {- i = i1 -} (λ j x → x)
          {- j = i0 -} (λ i x → unglue (i ∨ ~ i) x)
          {- j = i1 -} (λ i x → x)
    sq a i j x = glue {φ = (i ∨ ~ j) ∨ ~ (i ∨ ~ j)}
                      (λ { ((i ∨ ~ j) = i0) → x
                         ;     ((~ j) = i1) → unglue (i ∨ ~ i) x
                         ;         (i = i1) → x })
                      (unglue (i ∨ ~ i) x)

    bwd-fwd : ∀ x → bwd (fwd x) ≡ x
    bwd-fwd (inl b , x) = refl
    bwd-fwd (inr c , x) = refl
    bwd-fwd (push a i , x) j =
      hcomp (λ k → λ { (i = i0) → transp (λ _ → Σ (Pushout f g) E) (k ∨ j)
                                         (push a (~ (k ∨ j)) , ua-gluePath (e a) {x = x} refl (~ (k ∨ j)))
                     ; (i = i1) → transp (λ _ → Σ (Pushout f g) E) (k ∨ j)
                                         (inr (g a) , x)
                     ; (j = i1) → push a i , x })
            (transp (λ _ → Σ (Pushout f g) E) j (push a (i ∨ ~ j) , sq a i j x))

    isom : Iso (Σ (Pushout f g) E) (Pushout Σf Σg)
    isom = iso fwd bwd fwd-bwd bwd-fwd

  flatten : Σ (Pushout f g) E ≃ Pushout Σf Σg
  flatten = isoToEquiv FlattenIso.isom

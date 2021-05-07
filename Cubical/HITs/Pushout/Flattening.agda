{-

   The flattening lemma for pushouts (Lemma 8.5.3 in the HoTT book) proved in a cubical style.

   The proof in the HoTT book (the core lying in Lemma 6.12.2, the flattening lemma for coequalizers)
    consists mostly of long strings of equalities about transport. This proof follows almost
    entirely from definitional equalities involving glue/unglue.

-}
{-# OPTIONS --safe #-}
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

    fwd : Pushout Σf Σg → Σ (Pushout f g) E
    fwd (inl (b , x)) = (inl b , x)
    fwd (inr (c , x)) = (inr c , x)
    fwd (push (a , x) i) = (push a i , ua-gluePt (e a) i x)

    bwd : Σ (Pushout f g) E → Pushout Σf Σg
    bwd (inl b , x) = inl (b , x)
    bwd (inr c , x) = inr (c , x)
    bwd (push a i , x) = hcomp (λ j → λ { (i = i0) → push (a , x) (~ j)
                                        ; (i = i1) → inr (g a , x) })
                               (inr (g a , ua-unglue (e a) i x))

    bwd-fwd : ∀ x → bwd (fwd x) ≡ x
    bwd-fwd (inl (b , x)) = refl
    bwd-fwd (inr (c , x)) = refl
    bwd-fwd (push (a , x) i) j =
      hcomp (λ k → λ { (i = i0) → push (a , ua-gluePt (e a) i0 x) (~ k)
                     ; (i = i1) → inr (g a , ua-gluePt (e a) i1 x)
                     ; (j = i1) → push (a , x) (i ∨ ~ k) })
            (inr (g a , ua-unglue (e a) i (ua-gluePt (e a) i x)))
      -- Note: the (j = i1) case typechecks because of the definitional equalities:
      --  ua-gluePt e i0 x ≡ x , ua-gluePt e i1 x ≡ e .fst x,
      --  ua-unglue-glue : ua-unglue e i (ua-gluePt e i x) ≡ e .fst x

    -- essentially: ua-glue e (i ∨ ~ k) ∘ ua-unglue e i
    sq : ∀ {ℓ} {A B : Type ℓ} (e : A ≃ B)
         → SquareP (λ i k → ua e i → ua e (i ∨ ~ k))
      {- i = i0 -} (λ k x → ua-gluePt e (~ k) x)
      {- i = i1 -} (λ k x → x)
      {- k = i0 -} (λ i x → ua-unglue e i x)
      {- k = i1 -} (λ i x → x)
    sq e i k x = ua-glue e (i ∨ ~ k) (λ { ((i ∨ ~ k) = i0) → x })
                                     (inS (ua-unglue e i x))
      -- Note: this typechecks because of the definitional equalities:
      --  ua-unglue e i0 x ≡ e .fst x, ua-glue e i1 _ (inS y) ≡ y, ua-unglue e i1 x ≡ x,
      --  ua-glue-unglue : ua-glue e i (λ { (i = i0) → x }) (inS (ua-unglue e i x)) ≡ x

    fwd-bwd : ∀ x → fwd (bwd x) ≡ x
    fwd-bwd (inl b , x) = refl
    fwd-bwd (inr c , x) = refl
    fwd-bwd (push a i , x) j =
      -- `fwd` (or any function) takes hcomps to comps on a constant family, so we must use a comp here
      comp (λ _ → Σ (Pushout f g) E)
           (λ k → λ { (i = i0) → push a (~ k) , ua-gluePt (e a) (~ k) x
                    ; (i = i1) → inr (g a) , x
                    ; (j = i1) → push a (i ∨ ~ k) , sq (e a) i k x })
            (inr (g a) , ua-unglue (e a) i x)

    isom : Iso (Σ (Pushout f g) E) (Pushout Σf Σg)
    isom = iso bwd fwd bwd-fwd fwd-bwd

  flatten : Σ (Pushout f g) E ≃ Pushout Σf Σg
  flatten = isoToEquiv FlattenIso.isom

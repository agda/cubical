{-

Theory about equivalences (definitions are in Core/Glue.agda)

- isEquiv is a proposition ([isPropIsEquiv])
- Any isomorphism is an equivalence ([isoToEquiv])

There are more statements about equivalences in PathSplitEquiv.agda:

- if f is an equivalence then (cong f) is an equivalence
- if f is an equivalence then precomposition with f is an equivalence
- if f is an equivalence then postcomposition with f is an equivalence

-}
{-# OPTIONS --cubical --safe #-}
module Cubical.Foundations.Equiv where

open import Cubical.Core.Everything

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Nat

-- Proof using isPropIsContr. This is slow and the direct proof below is better
isPropIsEquiv' : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) → isProp (isEquiv f)
equiv-proof (isPropIsEquiv' f u0 u1 i) y =
  isPropIsContr (u0 .equiv-proof y) (u1 .equiv-proof y) i

-- Direct proof that computes quite ok (can be optimized further if
-- necessary, see:
-- https://github.com/mortberg/cubicaltt/blob/pi4s3_dimclosures/examples/brunerie2.ctt#L562
isPropIsEquiv : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) → isProp (isEquiv f)
equiv-proof (isPropIsEquiv f p q i) y =
  let p2 = p .equiv-proof y .snd
      q2 = q .equiv-proof y .snd
  in p2 (q .equiv-proof y .fst) i
   , λ w j → hcomp (λ k → λ { (i = i0) → p2 w j
                            ; (i = i1) → q2 w (j ∨ ~ k)
                            ; (j = i0) → p2 (q2 w (~ k)) i
                            ; (j = i1) → w })
                   (p2 w (i ∨ j))

equivEq : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (e f : A ≃ B) → (h : e .fst ≡ f .fst) → e ≡ f
equivEq e f h = λ i → (h i) , isProp→PathP isPropIsEquiv h (e .snd) (f .snd) i


isoToEquiv : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → Iso A B →  A ≃ B
isoToEquiv i = _ , isoToIsEquiv i

equivToIso : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → A ≃ B → Iso A B
equivToIso {A = A} {B = B} e = iso f g f-g g-f
  where
    f : A → B
    f = fst e

    g : B → A
    g b = e .snd .equiv-proof b .fst .fst

    f-g : ∀ b → f (g b) ≡ b
    f-g b = e .snd .equiv-proof b .fst .snd

    g-f : ∀ a → g (f a) ≡ a
    g-f a = cong fst (e .snd .equiv-proof (f a) .snd (a , refl))

module _ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (w : A ≃ B) where
  invEq : B → A
  invEq y = fst (fst (snd w .equiv-proof y))

  secEq : section invEq (w .fst)
  secEq x = λ i → fst (snd (snd w .equiv-proof (fst w x)) (x , (λ j → fst w x)) i)

  retEq : retract invEq (w .fst)
  retEq y = λ i → snd (fst (snd w .equiv-proof y)) i

invEquiv : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → A ≃ B → B ≃ A
invEquiv f = isoToEquiv (iso (invEq f) (fst f) (secEq f) (retEq f))

compEquiv : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : Set ℓ'} {C : Set ℓ''} →
            A ≃ B → B ≃ C → A ≃ C
compEquiv f g = isoToEquiv
                  (iso (λ x → g .fst (f .fst x)) 
                       (λ x → invEq f (invEq g x))
                       (λ y → (cong (g .fst) (retEq f (invEq g y))) ∙ (retEq g y))
                       (λ y → (cong (invEq f) (secEq g (f .fst y))) ∙ (secEq f y)))

-- module _ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'}  where
--   invEquivInvol : (f : A ≃ B) → invEquiv (invEquiv f) ≡ f
--   invEquivInvol f i .fst = fst f
--   invEquivInvol f i .snd = propIsEquiv (fst f) (snd (invEquiv (invEquiv f))) (snd f) i

PropEquiv→Equiv : ∀ {ℓ} {A B : Set ℓ} (Aprop : isProp A) (Bprop : isProp B) (f : A → B) (g : B → A) → (A ≃ B)
PropEquiv→Equiv Aprop Bprop f g = isoToEquiv (iso f g (λ b → Bprop (f (g b)) b) λ a → Aprop (g (f a)) a)

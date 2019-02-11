{-

Theory about equivalences (definitions are in Core/Glue.agda)

- isEquiv is a proposition ([isPropIsEquiv])
- Any isomorphism is an equivalence ([isoToEquiv])
- transport is an equivalence ([transportEquiv])

-}
{-# OPTIONS --cubical --safe #-}
module Cubical.Foundations.Equiv where

open import Cubical.Core.Everything

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism public


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

module _ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (w : A ≃ B) where
  invEq : B → A
  invEq y = fst (fst (snd w .equiv-proof y))

  secEq : section invEq (w .fst)
  secEq x = λ i → fst (snd (snd w .equiv-proof (fst w x)) (x , (λ j → fst w x)) i)

  retEq : retract invEq (w .fst)
  retEq y = λ i → snd (fst (snd w .equiv-proof y)) i

invEquiv : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → A ≃ B → B ≃ A
invEquiv f = isoToEquiv (invEq f) (fst f) (secEq f) (retEq f)

compEquiv : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : Set ℓ'} {C : Set ℓ''} →
            A ≃ B → B ≃ C → A ≃ C
compEquiv f g = isoToEquiv (λ x → g .fst (f .fst x))
                           (λ x → invEq f (invEq g x))
                           (λ y → compPath (cong (g .fst) (retEq f (invEq g y))) (retEq g y))
                           (λ y → compPath (cong (invEq f) (secEq g (f .fst y))) (secEq f y))


-- module _ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'}  where
--   invEquivInvol : (f : A ≃ B) → invEquiv (invEquiv f) ≡ f
--   invEquivInvol f i .fst = fst f
--   invEquivInvol f i .snd = propIsEquiv (fst f) (snd (invEquiv (invEquiv f))) (snd f) i


-- Transport is an equivalence
isEquivTransport : ∀ {ℓ} {A B : Set ℓ} (p : A ≡ B) → isEquiv (transport p)
isEquivTransport {A = A} =
  J (λ y x → isEquiv (transport x)) (isoToIsEquiv (transport refl) (transport refl) rem rem)
    where
    rem : (x : A) → transport refl (transport refl x) ≡ x
    rem x = compPath (cong (transport refl) (transportRefl x))
                     (transportRefl x)

transportEquiv : ∀ {ℓ} {A B : Set ℓ} → A ≡ B → A ≃ B
transportEquiv p = (transport p , isEquivTransport p)


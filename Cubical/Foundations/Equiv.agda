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

open import Cubical.Core.Glue

open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Data.Nat

private
  variable
    ℓ ℓ'  : Level
    A B C : Type ℓ

fiber : ∀ {A : Type ℓ} {B : Type ℓ'} (f : A → B) (y : B) → Type (ℓ-max ℓ ℓ')
fiber {A = A} f y = Σ[ x ∈ A ] f x ≡ y

equivIsEquiv : ∀ {A : Type ℓ} {B : Type ℓ'} (e : A ≃ B) → isEquiv (equivFun e)
equivIsEquiv e = snd e

equivCtr : ∀ {A : Type ℓ} {B : Type ℓ'} (e : A ≃ B) (y : B) → fiber (equivFun e) y
equivCtr e y = e .snd .equiv-proof y .fst

equivCtrPath : ∀ {A : Type ℓ} {B : Type ℓ'} (e : A ≃ B) (y : B) →
  (v : fiber (equivFun e) y) → Path _ (equivCtr e y) v
equivCtrPath e y = e .snd .equiv-proof y .snd

-- The identity equivalence
idIsEquiv : ∀ (A : Type ℓ) → isEquiv (idfun A)
equiv-proof (idIsEquiv A) y =
  ((y , refl) , λ z i → z .snd (~ i) , λ j → z .snd (~ i ∨ j))

idEquiv : ∀ (A : Type ℓ) → A ≃ A
idEquiv A = (idfun A , idIsEquiv A)

-- Proof using isPropIsContr. This is slow and the direct proof below is better

isPropIsEquiv' : (f : A → B) → isProp (isEquiv f)
equiv-proof (isPropIsEquiv' f u0 u1 i) y =
  isPropIsContr (u0 .equiv-proof y) (u1 .equiv-proof y) i

-- Direct proof that computes quite ok (can be optimized further if
-- necessary, see:
-- https://github.com/mortberg/cubicaltt/blob/pi4s3_dimclosures/examples/brunerie2.ctt#L562

isPropIsEquiv : (f : A → B) → isProp (isEquiv f)
equiv-proof (isPropIsEquiv f p q i) y =
  let p2 = p .equiv-proof y .snd
      q2 = q .equiv-proof y .snd
  in p2 (q .equiv-proof y .fst) i
   , λ w j → hcomp (λ k → λ { (i = i0) → p2 w j
                            ; (i = i1) → q2 w (j ∨ ~ k)
                            ; (j = i0) → p2 (q2 w (~ k)) i
                            ; (j = i1) → w })
                   (p2 w (i ∨ j))

equivEq : (e f : A ≃ B) → (h : e .fst ≡ f .fst) → e ≡ f
equivEq e f h = λ i → (h i) , isProp→PathP isPropIsEquiv h (e .snd) (f .snd) i

isoToEquiv : Iso A B →  A ≃ B
isoToEquiv i = _ , isoToIsEquiv i

module _ (w : A ≃ B) where
  invEq : B → A
  invEq y = fst (fst (snd w .equiv-proof y))

  secEq : section invEq (w .fst)
  secEq x = λ i → fst (snd (snd w .equiv-proof (fst w x)) (x , (λ j → fst w x)) i)

  retEq : retract invEq (w .fst)
  retEq y = λ i → snd (fst (snd w .equiv-proof y)) i

equivToIso : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → A ≃ B → Iso A B
equivToIso {A = A} {B = B} e = iso (e .fst) (invEq e ) (retEq e) (secEq e)

invEquiv : A ≃ B → B ≃ A
invEquiv f = isoToEquiv (iso (invEq f) (fst f) (secEq f) (retEq f))

compEquiv : A ≃ B → B ≃ C → A ≃ C
compEquiv f g = isoToEquiv
                  (iso (λ x → g .fst (f .fst x))
                       (λ x → invEq f (invEq g x))
                       (λ y → (cong (g .fst) (retEq f (invEq g y))) ∙ (retEq g y))
                       (λ y → (cong (invEq f) (secEq g (f .fst y))) ∙ (secEq f y)))

compIso : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} →
            Iso A B → Iso B C → Iso A C
compIso i j = equivToIso (compEquiv (isoToEquiv i) (isoToEquiv j))

LiftEquiv : {A : Type ℓ} → A ≃ Lift {i = ℓ} {j = ℓ'} A
LiftEquiv = isoToEquiv (iso lift lower (λ _ → refl) (λ _ → refl))

-- module _ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}  where
--   invEquivInvol : (f : A ≃ B) → invEquiv (invEquiv f) ≡ f
--   invEquivInvol f i .fst = fst f
--   invEquivInvol f i .snd = propIsEquiv (fst f) (snd (invEquiv (invEquiv f))) (snd f) i

PropEquiv→Equiv : (Aprop : isProp A) (Bprop : isProp B) (f : A → B) (g : B → A) → (A ≃ B)
PropEquiv→Equiv Aprop Bprop f g = isoToEquiv (iso f g (λ b → Bprop (f (g b)) b) λ a → Aprop (g (f a)) a)

homotopyNatural : {f g : A → B} (H : ∀ a → f a ≡ g a) {x y : A} (p : x ≡ y) →
                  H x ∙ cong g p ≡ cong f p ∙ H y
homotopyNatural H p = homotopyNatural' H p ∙ □≡∙ _ _
  where
  homotopyNatural' : {f g : A → B} (H : ∀ a → f a ≡ g a) {x y : A} (p : x ≡ y) →
                     H x ∙ cong g p ≡ cong f p □ H y
  homotopyNatural' {f = f} {g = g} H {x} {y} p i j =
    hcomp (λ k → λ { (i = i0) → compPath-filler (H x) (cong g p) k j
                   ; (i = i1) → compPath'-filler (cong f p) (H y) k j
                   ; (j = i0) → cong f p (i ∧ (~ k))
                   ; (j = i1) → cong g p (i ∨ k) })
          (H (p i) j)

Hfa≡fHa : ∀ {A : Type ℓ} (f : A → A) → (H : ∀ a → f a ≡ a) → ∀ a → H (f a) ≡ cong f (H a)
Hfa≡fHa {A = A} f H a =
  H (f a)                          ≡⟨ rUnit (H (f a)) ⟩
  H (f a) ∙ refl                   ≡⟨ cong (_∙_ (H (f a))) (sym (rCancel (H a))) ⟩
  H (f a) ∙ H a ∙ sym (H a)        ≡⟨ assoc _ _ _ ⟩
  (H (f a) ∙ H a) ∙ sym (H a)      ≡⟨ cong (λ x →  x ∙ (sym (H a))) (homotopyNatural H (H a)) ⟩
  (cong f (H a) ∙ H a) ∙ sym (H a) ≡⟨ sym (assoc _ _ _) ⟩
  cong f (H a) ∙ H a ∙ sym (H a)   ≡⟨ cong (_∙_ (cong f (H a))) (rCancel _) ⟩
  cong f (H a) ∙ refl              ≡⟨ sym (rUnit _) ⟩
  cong f (H a) ∎

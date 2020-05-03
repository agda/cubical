{-

Theory about equivalences

Definitions are in Core/Glue.agda but re-exported by this module

- isEquiv is a proposition ([isPropIsEquiv])
- Any isomorphism is an equivalence ([isoToEquiv])

There are more statements about equivalences in Equiv/Properties.agda:

- if f is an equivalence then (cong f) is an equivalence
- if f is an equivalence then precomposition with f is an equivalence
- if f is an equivalence then postcomposition with f is an equivalence

-}
{-# OPTIONS --cubical --safe #-}
module Cubical.Foundations.Equiv where

open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Foundations.Equiv.Base public

private
  variable
    ℓ ℓ' ℓ''  : Level
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
equivEq e f h = λ i → (h i) , isProp→PathP (λ i → isPropIsEquiv (h i)) (e .snd) (f .snd) i

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

invEquivIdEquiv : (A : Type ℓ) → invEquiv (idEquiv A) ≡ idEquiv A
invEquivIdEquiv _ = equivEq _ _ refl

compEquiv : A ≃ B → B ≃ C → A ≃ C
compEquiv f g = isoToEquiv
                  (iso (λ x → g .fst (f .fst x))
                       (λ x → invEq f (invEq g x))
                       (λ y → (cong (g .fst) (retEq f (invEq g y))) ∙ (retEq g y))
                       (λ y → (cong (invEq f) (secEq g (f .fst y))) ∙ (secEq f y)))

compEquivIdEquiv : {A B : Type ℓ} (e : A ≃ B) → compEquiv (idEquiv A) e ≡ e
compEquivIdEquiv e = equivEq _ _ refl

compEquivEquivId : {A B : Type ℓ} (e : A ≃ B) → compEquiv e (idEquiv B) ≡ e
compEquivEquivId e = equivEq _ _ refl

invEquiv-is-rinv : {A B : Type ℓ} (e : A ≃ B) → compEquiv e (invEquiv e) ≡ idEquiv A
invEquiv-is-rinv e = equivEq _ _ (funExt (secEq e))

invEquiv-is-linv : {A B : Type ℓ} (e : A ≃ B) → compEquiv (invEquiv e) e ≡ idEquiv B
invEquiv-is-linv e = equivEq _ _ (funExt (retEq e))

compEquiv-assoc : {A B C D : Type ℓ} (f : A ≃ B) (g : B ≃ C) (h : C ≃ D)
        → compEquiv f (compEquiv g h) ≡ compEquiv (compEquiv f g) h
compEquiv-assoc f g h = equivEq _ _ refl

LiftEquiv : {A : Type ℓ} → A ≃ Lift {i = ℓ} {j = ℓ'} A
LiftEquiv = isoToEquiv (iso lift lower (λ _ → refl) (λ _ → refl))

-- module _ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}  where
--   invEquivInvol : (f : A ≃ B) → invEquiv (invEquiv f) ≡ f
--   invEquivInvol f i .fst = fst f
--   invEquivInvol f i .snd = propIsEquiv (fst f) (snd (invEquiv (invEquiv f))) (snd f) i

Contr→Equiv : isContr A → isContr B → A ≃ B
Contr→Equiv Actr Bctr = isoToEquiv (iso (λ _ → fst Bctr) (λ _ → fst Actr) (snd Bctr) (snd Actr))

PropEquiv→Equiv : (Aprop : isProp A) (Bprop : isProp B) (f : A → B) (g : B → A) → (A ≃ B)
PropEquiv→Equiv Aprop Bprop f g = isoToEquiv (iso f g (λ b → Bprop (f (g b)) b) λ a → Aprop (g (f a)) a)

homotopyNatural : {f g : A → B} (H : ∀ a → f a ≡ g a) {x y : A} (p : x ≡ y) →
                  H x ∙ cong g p ≡ cong f p ∙ H y
homotopyNatural {f = f} {g = g} H {x} {y} p i j =
    hcomp (λ k → λ { (i = i0) → compPath-filler (H x) (cong g p) k j
                   ; (i = i1) → compPath-filler' (cong f p) (H y) k j
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

invEq≡→equivFun≡ : ∀ (e : A ≃ B) {x y} → invEq e x ≡ y → equivFun e y ≡ x
invEq≡→equivFun≡ e {x} p = cong (equivFun e) (sym p) ∙ retEq e x

equivPi
  : ∀{F : A → Set ℓ} {G : A → Set ℓ'}
  → ((x : A) → F x ≃ G x) → (((x : A) → F x) ≃ ((x : A) → G x))
equivPi k .fst f x = k x .fst (f x)
equivPi k .snd .equiv-proof f
  .fst .fst x = equivCtr (k x) (f x) .fst
equivPi k .snd .equiv-proof f
  .fst .snd i x = equivCtr (k x) (f x) .snd i
equivPi k .snd .equiv-proof f
  .snd (g , p) i .fst x = equivCtrPath (k x) (f x) (g x , λ j → p j x) i .fst
equivPi k .snd .equiv-proof f
  .snd (g , p) i .snd j x = equivCtrPath (k x) (f x) (g x , λ k → p k x) i .snd j

-- Some helpful notation:
_≃⟨_⟩_ : (X : Type ℓ) → (X ≃ B) → (B ≃ C) → (X ≃ C)
_ ≃⟨ f ⟩ g = compEquiv f g

_■ : (X : Type ℓ) → (X ≃ X)
_■ = idEquiv

infixr  0 _≃⟨_⟩_
infix   1 _■

composesToId→Equiv : (f : A → B) (g : B → A) → f ∘ g ≡ idfun B → isEquiv f → isEquiv g
composesToId→Equiv f g id iseqf =
  isoToIsEquiv
    (iso g
         f
         (λ b → (λ i → (equiv-proof iseqf (f b) .snd (g (f b) ,
                          cong (λ h → h (f b)) id) (~ i))  .fst )
                 ∙ cong (λ x → (equiv-proof iseqf (f b) .fst .fst )) id
                 ∙ λ i → (equiv-proof iseqf (f b) .snd) (b , refl) i .fst )
         λ a → cong (λ f → f a) id)

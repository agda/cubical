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
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Foundations.Equiv where

open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Foundations.Equiv.Base public

private
  variable
    ℓ ℓ' ℓ''  : Level
    A B C D : Type ℓ

equivIsEquiv : (e : A ≃ B) → isEquiv (equivFun e)
equivIsEquiv e = snd e

equivCtr : (e : A ≃ B) (y : B) → fiber (equivFun e) y
equivCtr e y = e .snd .equiv-proof y .fst

equivCtrPath : (e : A ≃ B) (y : B) →
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

module _ {f : A → B} (equivF : isEquiv f) where
  invIsEq : B → A
  invIsEq y = equivF .equiv-proof y .fst .fst

  secIsEq : section f invIsEq
  secIsEq y = equivF .equiv-proof y .fst .snd

  retIsEq : retract f invIsEq
  retIsEq a i = equivF .equiv-proof (f a) .snd (a , refl) i .fst

  commSqIsEq : ∀ a → Square (secIsEq (f a)) refl (cong f (retIsEq a)) refl
  commSqIsEq a i = equivF .equiv-proof (f a) .snd (a , refl) i .snd

module _ (w : A ≃ B) where
  invEq : B → A
  invEq = invIsEq (snd w)

  secEq : section invEq (w .fst)
  secEq = retIsEq (snd w)

  retEq : retract invEq (w .fst)
  retEq = secIsEq (snd w)

open Iso

equivToIso : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → A ≃ B → Iso A B
fun (equivToIso e) = e .fst
inv (equivToIso e) = invEq e
rightInv (equivToIso e) = retEq e
leftInv (equivToIso e)  = secEq e

-- TODO: there should be a direct proof of this that doesn't use equivToIso
invEquiv : A ≃ B → B ≃ A
invEquiv e = isoToEquiv (invIso (equivToIso e))

invEquivIdEquiv : (A : Type ℓ) → invEquiv (idEquiv A) ≡ idEquiv A
invEquivIdEquiv _ = equivEq _ _ refl

-- TODO: there should be a direct proof of this that doesn't use equivToIso
compEquiv : A ≃ B → B ≃ C → A ≃ C
compEquiv f g = isoToEquiv (compIso (equivToIso f) (equivToIso g))

compEquivIdEquiv : (e : A ≃ B) → compEquiv (idEquiv A) e ≡ e
compEquivIdEquiv e = equivEq _ _ refl

compEquivEquivId : (e : A ≃ B) → compEquiv e (idEquiv B) ≡ e
compEquivEquivId e = equivEq _ _ refl

invEquiv-is-rinv : (e : A ≃ B) → compEquiv e (invEquiv e) ≡ idEquiv A
invEquiv-is-rinv e = equivEq _ _ (funExt (secEq e))

invEquiv-is-linv : (e : A ≃ B) → compEquiv (invEquiv e) e ≡ idEquiv B
invEquiv-is-linv e = equivEq _ _ (funExt (retEq e))

compEquiv-assoc : (f : A ≃ B) (g : B ≃ C) (h : C ≃ D)
                → compEquiv f (compEquiv g h) ≡ compEquiv (compEquiv f g) h
compEquiv-assoc f g h = equivEq _ _ refl

LiftEquiv : A ≃ Lift {i = ℓ} {j = ℓ'} A
LiftEquiv .fst a .lower = a
LiftEquiv .snd .equiv-proof a+ .fst .fst = a+ .lower
LiftEquiv .snd .equiv-proof _ .fst .snd = refl
LiftEquiv .snd .equiv-proof _ .snd (_ , p) i .fst = p (~ i) .lower
LiftEquiv .snd .equiv-proof _ .snd (_ , p) i .snd j = p (~ i ∨ j)

Lift≃Lift : (e : A ≃ B) → Lift {j = ℓ'} A ≃ Lift {j = ℓ''} B
Lift≃Lift e .fst a .lower = e .fst (a .lower)
Lift≃Lift e .snd .equiv-proof b .fst .fst .lower = invEq e (b .lower)
Lift≃Lift e .snd .equiv-proof b .fst .snd i .lower =
  e .snd .equiv-proof (b .lower) .fst .snd i
Lift≃Lift e .snd .equiv-proof b .snd (a , p) i .fst .lower =
  e .snd .equiv-proof (b .lower) .snd (a .lower , cong lower p) i .fst
Lift≃Lift e .snd .equiv-proof b .snd (a , p) i .snd j .lower =
  e .snd .equiv-proof (b .lower) .snd (a .lower , cong lower p) i .snd j

isContr→Equiv : isContr A → isContr B → A ≃ B
isContr→Equiv Actr Bctr = isoToEquiv (isContr→Iso Actr Bctr)

isPropEquiv→Equiv : (Aprop : isProp A) (Bprop : isProp B) (f : A → B) (g : B → A) → A ≃ B
isPropEquiv→Equiv Aprop Bprop f g = isoToEquiv (isProp→Iso Aprop Bprop f g)

invEq≡→equivFun≡ : ∀ (e : A ≃ B) {x y} → invEq e x ≡ y → equivFun e y ≡ x
invEq≡→equivFun≡ e {x} p = cong (equivFun e) (sym p) ∙ retEq e x

equivPi : ∀ {F : A → Type ℓ} {G : A → Type ℓ'}
        → ((x : A) → F x ≃ G x) → ((x : A) → F x) ≃ ((x : A) → G x)
equivPi k .fst f x = k x .fst (f x)
equivPi k .snd .equiv-proof f .fst .fst x   = equivCtr (k x) (f x) .fst
equivPi k .snd .equiv-proof f .fst .snd i x = equivCtr (k x) (f x) .snd i
equivPi k .snd .equiv-proof f .snd (g , p) i .fst x =
  equivCtrPath (k x) (f x) (g x , λ j → p j x) i .fst
equivPi k .snd .equiv-proof f .snd (g , p) i .snd j x =
  equivCtrPath (k x) (f x) (g x , λ k → p k x) i .snd j

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
    (iso g f
         (λ b → (λ i → equiv-proof iseqf (f b) .snd (g (f b) , cong (λ h → h (f b)) id) (~ i) .fst)
                ∙∙ cong (λ x → equiv-proof iseqf (f b) .fst .fst) id
                ∙∙ λ i → equiv-proof iseqf (f b) .snd (b , refl) i .fst)
         λ a i → id i a)

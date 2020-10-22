{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.HITs.Susp.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Path

open import Cubical.Data.Bool
open import Cubical.HITs.Join
open import Cubical.HITs.Susp.Base

open Iso

Susp-iso-joinBool : ∀ {ℓ} {A : Type ℓ} → Iso (Susp A) (join A Bool)
fun Susp-iso-joinBool north = inr true
fun Susp-iso-joinBool south = inr false
fun Susp-iso-joinBool (merid a i) = (sym (push a true) ∙ push a false) i
inv Susp-iso-joinBool (inr true ) = north
inv Susp-iso-joinBool (inr false) = south
inv Susp-iso-joinBool (inl _) = north
inv Susp-iso-joinBool (push a true  i) = north
inv Susp-iso-joinBool (push a false i) = merid a i
rightInv Susp-iso-joinBool (inr true ) = refl
rightInv Susp-iso-joinBool (inr false) = refl
rightInv Susp-iso-joinBool (inl a) = sym (push a true)
rightInv Susp-iso-joinBool (push a true  i) j = push a true (i ∨ ~ j)
rightInv Susp-iso-joinBool (push a false i) j
  = hcomp (λ k → λ { (i = i0) → push a true (~ j)
                   ; (i = i1) → push a false k
                   ; (j = i1) → push a false (i ∧ k) })
          (push a true (~ i ∧ ~ j))
leftInv Susp-iso-joinBool north = refl
leftInv Susp-iso-joinBool south = refl
leftInv (Susp-iso-joinBool {A = A}) (merid a i) j
  = hcomp (λ k → λ { (i = i0) → transp (λ _ → Susp A) (k ∨ j) north
                   ; (i = i1) → transp (λ _ → Susp A) (k ∨ j) (merid a k)
                   ; (j = i1) → merid a (i ∧ k) })
          (transp (λ _ → Susp A) j north)

Susp≃joinBool : ∀ {ℓ} {A : Type ℓ} → Susp A ≃ join A Bool
Susp≃joinBool = isoToEquiv Susp-iso-joinBool

Susp≡joinBool : ∀ {ℓ} {A : Type ℓ} → Susp A ≡ join A Bool
Susp≡joinBool = isoToPath Susp-iso-joinBool

congSuspEquiv : ∀ {ℓ} {A B : Type ℓ} → A ≃ B → Susp A ≃ Susp B
congSuspEquiv {ℓ} {A} {B} h = isoToEquiv isom
  where isom : Iso (Susp A) (Susp B)
        Iso.fun isom north = north
        Iso.fun isom south = south
        Iso.fun isom (merid a i) = merid (fst h a) i
        Iso.inv isom north = north
        Iso.inv isom south = south
        Iso.inv isom (merid a i) = merid (invEq h a) i
        Iso.rightInv isom north = refl
        Iso.rightInv isom south = refl
        Iso.rightInv isom (merid a i) j = merid (retEq h a j) i
        Iso.leftInv isom north = refl
        Iso.leftInv isom south = refl
        Iso.leftInv isom (merid a i) j = merid (secEq h a j) i

suspToPropElim : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Susp A → Type ℓ'} (a : A)
                 → ((x : Susp A) → isProp (B x))
                 → B north
                 → (x : Susp A) → B x
suspToPropElim a isProp Bnorth north = Bnorth
suspToPropElim {B = B} a isProp Bnorth south = subst B (merid a) Bnorth
suspToPropElim {B = B} a isProp Bnorth (merid a₁ i) =
  isOfHLevel→isOfHLevelDep 1 isProp Bnorth (subst B (merid a) Bnorth) (merid a₁) i

suspToPropElim2 : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Susp A → Susp A → Type ℓ'} (a : A)
                 → ((x y : Susp A) → isProp (B x y))
                 → B north north
                 → (x y : Susp A) → B x y
suspToPropElim2 _ _ Bnorth north north = Bnorth
suspToPropElim2 {B = B} a _ Bnorth north south = subst (B north) (merid a) Bnorth
suspToPropElim2 {B = B} a isprop Bnorth north (merid x i) =
  isProp→PathP (λ i → isprop north (merid x i))
               Bnorth (subst (B north) (merid a) Bnorth) i
suspToPropElim2 {B = B} a _ Bnorth south north = subst (λ x → B x north) (merid a) Bnorth
suspToPropElim2 {B = B} a _ Bnorth south south = subst (λ x → B x x) (merid a) Bnorth
suspToPropElim2 {B = B} a isprop Bnorth south (merid x i) =
  isProp→PathP (λ i → isprop south (merid x i))
               (subst (λ x → B x north) (merid a) Bnorth)
               (subst (λ x → B x x) (merid a) Bnorth) i
suspToPropElim2 {B = B} a isprop Bnorth (merid x i) north =
  isProp→PathP (λ i → isprop (merid x i) north)
               Bnorth (subst (λ x → B x north) (merid a) Bnorth) i
suspToPropElim2 {B = B} a isprop Bnorth (merid x i) south =
  isProp→PathP (λ i → isprop (merid x i) south)
               (subst (B north) (merid a) Bnorth)
               (subst (λ x → B x x) (merid a) Bnorth) i
suspToPropElim2 {B = B} a isprop Bnorth (merid x i) (merid y j) =
  isSet→SquareP (λ i j → isOfHLevelSuc 1 (isprop _ _))
     (isProp→PathP (λ i₁ → isprop north (merid y i₁)) Bnorth
                   (subst (B north) (merid a) Bnorth))
     (isProp→PathP (λ i₁ → isprop south (merid y i₁))
                   (subst (λ x₁ → B x₁ north) (merid a) Bnorth)
                   (subst (λ x₁ → B x₁ x₁) (merid a) Bnorth))
     (isProp→PathP (λ i₁ → isprop (merid x i₁) north) Bnorth
                   (subst (λ x₁ → B x₁ north) (merid a) Bnorth))
     (isProp→PathP (λ i₁ → isprop (merid x i₁) south)
                   (subst (B north) (merid a) Bnorth)
                   (subst (λ x₁ → B x₁ x₁) (merid a) Bnorth)) i j
{- Clever proof:
suspToPropElim2 a isProp Bnorth =
  suspToPropElim a (λ x → isOfHLevelΠ 1 λ y → isProp x y)
                   (suspToPropElim a (λ x → isProp north x) Bnorth)
-}

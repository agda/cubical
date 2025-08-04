{-

This file contains:

- Definition of the Bouquet of circles of a type aka wedge of A circles

-}
module Cubical.HITs.Bouquet.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Unit

open import Cubical.HITs.Bouquet.Base
open import Cubical.HITs.SphereBouquet
open import Cubical.HITs.Pushout
open import Cubical.HITs.S1

open import Cubical.Homotopy.Loopspace

private
  variable
    ℓ : Level

elimPropBouquet : ∀ {ℓ ℓ'} {A : Type ℓ}
  {B : Bouquet A → Type ℓ'}
  (pr : (x : _) → isProp (B x))
  (b : B base)
  → (x  : Bouquet A) → B x
elimPropBouquet pr b base = b
elimPropBouquet {B = B} pr b (loop x i) =
  isProp→PathP {B = λ i → B (loop x i)} (λ _ → pr _) b b i

module _ {ℓ} {A : Type ℓ} where
  SphereBouquet→Bouquet : SphereBouquet 1 A → Bouquet A
  SphereBouquet→Bouquet (inl x) = base
  SphereBouquet→Bouquet (inr (s , base)) = base
  SphereBouquet→Bouquet (inr (s , loop i)) = loop s i
  SphereBouquet→Bouquet (push a i) = base

  Bouquet→SphereBouquet : Bouquet A → SphereBouquet 1 A
  Bouquet→SphereBouquet base = inl tt
  Bouquet→SphereBouquet (loop x i) =
    (push x ∙∙ (λ i → inr (x , loop i)) ∙∙ sym (push x)) i

  Iso-SphereBouquet-Bouquet : Iso (SphereBouquet 1 A) (Bouquet A)
  Iso.fun Iso-SphereBouquet-Bouquet = SphereBouquet→Bouquet
  Iso.inv Iso-SphereBouquet-Bouquet = Bouquet→SphereBouquet
  Iso.rightInv Iso-SphereBouquet-Bouquet base = refl
  Iso.rightInv Iso-SphereBouquet-Bouquet (loop x i) j =
    SphereBouquet→Bouquet
      (doubleCompPath-filler (push x) (λ i → inr (x , loop i)) (sym (push x)) (~ j) i)
  Iso.leftInv Iso-SphereBouquet-Bouquet (inl x) = refl
  Iso.leftInv Iso-SphereBouquet-Bouquet (inr (s , base)) = push s
  Iso.leftInv Iso-SphereBouquet-Bouquet (inr (s , loop i)) j =
    doubleCompPath-filler (push s) (λ i → inr (s , loop i)) (sym (push s)) (~ j) i
  Iso.leftInv Iso-SphereBouquet-Bouquet (push a i) j = push a (i ∧ j)

  Bouquet≃∙SphereBouquet : SphereBouquet∙ 1 A ≃∙ Bouquet A , base
  fst Bouquet≃∙SphereBouquet = isoToEquiv (Iso-SphereBouquet-Bouquet)
  snd Bouquet≃∙SphereBouquet = refl

module _ {ℓ ℓ'} {A : Type ℓ} (B : Pointed ℓ') where
  BouquetFun∙→Ω : (Bouquet∙ A →∙ B) → (A → Ω B .fst)
  BouquetFun∙→Ω f x = sym (snd f) ∙∙ cong (fst f) (loop x) ∙∙ snd f

  Ω→BouquetFun∙ : (A → Ω B .fst) → (Bouquet∙ A →∙ B)
  fst (Ω→BouquetFun∙ f) base = pt B
  fst (Ω→BouquetFun∙ f) (loop x i) = f x i
  snd (Ω→BouquetFun∙ f) = refl

  CharacBouquet∙Iso : Iso (Bouquet∙ A →∙ B) (A → Ω B .fst)
  Iso.fun CharacBouquet∙Iso = BouquetFun∙→Ω
  Iso.inv CharacBouquet∙Iso = Ω→BouquetFun∙
  Iso.rightInv CharacBouquet∙Iso h i x j =
    compPath-filler (h x) refl (~ i) j
  fst (Iso.leftInv CharacBouquet∙Iso h i) base = snd h (~ i)
  fst (Iso.leftInv CharacBouquet∙Iso h i) (loop x j) =
    doubleCompPath-filler (sym (snd h)) (cong (fst h) (loop x)) (snd h) (~ i) j
  snd (Iso.leftInv CharacBouquet∙Iso h i) j = snd h (~ i ∨ j)

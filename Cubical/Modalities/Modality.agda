{-# OPTIONS --safe #-}
module Cubical.Modalities.Modality where

{-
  translated from
  https://github.com/HoTT/HoTT-Agda/blob/master/core/lib/types/Modality.agda
-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv.Properties

record Modality ℓ : Type (ℓ-suc ℓ) where
  field
    isModal : Type ℓ → Type ℓ
    isPropIsModal : {A : Type ℓ} → isProp (isModal A)

    ◯ : Type ℓ → Type ℓ                                  -- \ciO
    ◯-isModal : {A : Type ℓ} → isModal (◯ A)

    η : {A : Type ℓ} → A → ◯ A

    ◯-elim : {A : Type ℓ} {B : ◯ A → Type ℓ}
      (B-modal : (x : ◯ A) → isModal (B x))
      → ((x : A) → (B (η x))) → ((x : ◯ A) → B x)

    ◯-elim-β : {A : Type ℓ} {B : ◯ A → Type ℓ}
      (B-modal : (x : ◯ A) → isModal (B x)) (f : (x : A) → (B (η x)))
      → (a : A) → ◯-elim B-modal f (η a) ≡ f a

    ◯-=-isModal : {A : Type ℓ} (x y : ◯ A) → isModal (x ≡ y)

  ◯-Types : Type (ℓ-suc ℓ)
  ◯-Types = TypeWithStr ℓ isModal

  {- elimination rules -}

  module ◯Elim {A : Type ℓ} {B : ◯ A → Type ℓ}
    (B-modal : (x : ◯ A) → isModal (B x)) (η* : (x : A) → (B (η x))) where
      f : (x : ◯ A) → B x
      f = ◯-elim B-modal η*
      η-β : (a : A) → ◯-elim B-modal η* (η a) ≡ η* a
      η-β = ◯-elim-β B-modal η*

  module ◯Rec {A : Type ℓ} {B : Type ℓ}
         (B-modal : isModal B) (η* : A → B)
      = ◯Elim (λ _ → B-modal) η*

  ◯-rec = ◯Rec.f
  ◯-rec-β = ◯Rec.η-β

  {- functoriality -}

  module ◯Fmap {A B : Type ℓ} (f : A → B) =
      ◯Rec ◯-isModal (η ∘ f)

  ◯-map = ◯Fmap.f
  ◯-map-β = ◯Fmap.η-β

  ◯-preservesEquiv : {A B : Type ℓ} (f : A → B) → isEquiv f → isEquiv (◯-map f)
  ◯-preservesEquiv f f-ise = isoToIsEquiv (iso _ (◯-map inv) to-from from-to) where
    open Iso (equivToIso (f , f-ise))
    to-from : ∀ ◯b → ◯-map f (◯-map inv ◯b) ≡ ◯b
    to-from = ◯-elim
      (λ ◯b → ◯-=-isModal (◯-map f (◯-map inv ◯b)) ◯b)
      (λ b → cong (◯-map f) (◯-map-β inv b) ∙ ◯-map-β f (inv b) ∙ cong η (rightInv b))
    from-to : ∀ ◯a → ◯-map inv (◯-map f ◯a) ≡ ◯a
    from-to = ◯-elim
        (λ ◯a → ◯-=-isModal (◯-map inv (◯-map f ◯a)) ◯a)
        (λ a → cong (◯-map inv) (◯-map-β f a) ∙ ◯-map-β inv (f a) ∙ cong η (leftInv a))


  ◯-equiv : {A B : Type ℓ} → A ≃ B → ◯ A ≃ ◯ B
  ◯-equiv (f , f-ise) = ◯-map f , ◯-preservesEquiv f f-ise


  {- equivalences preserve being modal -}

  equivPreservesIsModal : {A B : Type ℓ} → A ≃ B → isModal A → isModal B
  equivPreservesIsModal eq = subst isModal (ua eq)


  {- modal types and [η] being an equivalence -}

  isModalToIso : {A : Type ℓ} → isModal A → Iso A (◯ A)
  Iso.fun (isModalToIso _) = η
  Iso.inv (isModalToIso w) = ◯-rec w (idfun _)
  Iso.rightInv (isModalToIso w) = ◯-elim (λ _ → ◯-=-isModal _ _) (λ a₀ → cong η (◯-rec-β w (idfun _) a₀))
  Iso.leftInv (isModalToIso w) = ◯-rec-β w (idfun _)

  isModalToIsEquiv : {A : Type ℓ} → isModal A → isEquiv (η {A})
  isModalToIsEquiv {A} w = isoToIsEquiv (isModalToIso w)

  isEquivToIsModal : {A : Type ℓ} → isEquiv (η {A}) → isModal A
  isEquivToIsModal {A} eq = equivPreservesIsModal (invEquiv (η , eq)) ◯-isModal

  retractIsModal : {A B : Type ℓ} (w : isModal A)
      (f : A → B) (g : B → A) (r : (b : B) → f (g b) ≡ b) →
      isModal B
  retractIsModal {A} {B} w f g r =
    isEquivToIsModal
      (isoToIsEquiv (iso η η-inv inv-l inv-r))
    where η-inv : ◯ B → B
          η-inv = f ∘ (◯-rec w g)

          inv-r : (b : B) → η-inv (η b) ≡ b
          inv-r b = cong f (◯-rec-β w g b) ∙ r b

          inv-l : (b : ◯ B) → η (η-inv b) ≡ b
          inv-l = ◯-elim (λ b → ◯-=-isModal _ _) (λ b → cong η (inv-r b))

  {- function types with modal codomain are modal -}

  Π-isModal : {A : Type ℓ} {B : A → Type ℓ}
            (w : (a : A) → isModal (B a)) → isModal ((x : A) → B x)
  Π-isModal {A} {B} w = retractIsModal {◯ _} {(x : A) → B x} ◯-isModal η-inv η r

      where η-inv : ◯ ((x : A) → B x) → (x : A) → B x
            η-inv φ' a = ◯-rec (w a) (λ φ → φ a) φ'

            r : (φ : (x : A) →  B x) → η-inv (η φ) ≡ φ
            r φ = funExt (λ a → ◯-rec-β (w a) (λ φ₀ → φ₀ a) φ)

  →-isModal : {A B : Type ℓ} → isModal B → isModal (A → B)
  →-isModal w = Π-isModal (λ _ → w)

  {- sigma types of a modal dependent type with modal base are modal -}

  Σ-isModal : {A : Type ℓ} (B : A → Type ℓ)
    → isModal A → ((a : A) → isModal (B a))
    → isModal (Σ A B)
  Σ-isModal {A} B A-modal B-modal =
    retractIsModal {◯ (Σ A B)} {Σ A B} ◯-isModal η-inv η r

    where h : ◯ (Σ A B) → A
          h = ◯-rec A-modal fst

          h-β : (x : Σ A B) → h (η x) ≡ fst x
          h-β = ◯-rec-β A-modal fst

          f : (j : I) → (x : Σ A B) → B (h-β x j)
          f j x = transp (λ i → B (h-β x ((~ i) ∨ j))) j (snd x)

          k : (y : ◯ (Σ A B)) → B (h y)
          k = ◯-elim (B-modal ∘ h) (f i0)

          η-inv : ◯ (Σ A B) → Σ A B
          η-inv y = h y , k y

          p : (x : Σ A B) → k (η x) ≡ f i0 x
          p = ◯-elim-β (B-modal ∘ h) (f i0)

          almost : (x : Σ A B) → (h (η x) , f i0 x) ≡ x
          almost x i = h-β x i , f i x

          r : (x : Σ A B) → η-inv (η x) ≡ x
          r x = (λ i → h (η x) , p x i) ∙ (almost x)

  isModal≡ : {A : Type ℓ} → (isModal A) → {x y : A} → (isModal (x ≡ y))
  isModal≡ A-modal = equivPreservesIsModal (invEquiv (congEquiv (η , (isModalToIsEquiv A-modal)))) (◯-=-isModal _ _)

  ◯-preservesProp : {A : Type ℓ} → (isProp A) → (isProp (◯ A))
  ◯-preservesProp pA u = ◯-elim (λ z → ◯-=-isModal _ _)
                         λ b → ◯-elim (λ x → ◯-=-isModal _ _) (λ a → cong η (pA a b)) u

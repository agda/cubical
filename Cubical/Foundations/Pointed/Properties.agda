{-# OPTIONS --safe #-}
module Cubical.Foundations.Pointed.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed.Base
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sigma

private
  variable
    ℓ ℓ' ℓA ℓB ℓC ℓD : Level

-- the default pointed Π-type: A is pointed, and B has a base point in the chosen fiber
Π∙ : (A : Pointed ℓ) (B : typ A → Type ℓ') (ptB : B (pt A)) → Type (ℓ-max ℓ ℓ')
Π∙ A B ptB = Σ[ f ∈ ((a : typ A) → B a) ] f (pt A) ≡ ptB

-- the unpointed Π-type becomes a pointed type if the fibers are all pointed
Πᵘ∙ : (A : Type ℓ) (B : A → Pointed ℓ') → Pointed (ℓ-max ℓ ℓ')
Πᵘ∙ A B .fst = ∀ a → typ (B a)
Πᵘ∙ A B .snd a = pt (B a)

-- if the base and all fibers are pointed, we have the pointed pointed Π-type
Πᵖ∙ : (A : Pointed ℓ) (B : typ A → Pointed ℓ') → Pointed (ℓ-max ℓ ℓ')
Πᵖ∙ A B .fst = Π∙ A (typ ∘ B) (pt (B (pt A)))
Πᵖ∙ A B  .snd .fst a = pt (B a)
Πᵖ∙ A B  .snd .snd = refl

-- the default pointed Σ-type is just the Σ-type, but as a pointed type
Σ∙ : (A : Pointed ℓ) (B : typ A → Type ℓ') (ptB : B (pt A)) → Pointed (ℓ-max ℓ ℓ')
Σ∙ A B ptB .fst = Σ[ a ∈ typ A ] B a
Σ∙ A B ptB .snd .fst = pt A
Σ∙ A B ptB .snd .snd = ptB

-- version if B is a family of pointed types
Σᵖ∙ : (A : Pointed ℓ) (B : typ A → Pointed ℓ') → Pointed (ℓ-max ℓ ℓ')
Σᵖ∙ A B = Σ∙ A (typ ∘ B) (pt (B (pt A)))

_×∙_ : (A∙ : Pointed ℓ) (B∙ : Pointed ℓ') → Pointed (ℓ-max ℓ ℓ')
(A∙ ×∙ B∙) .fst = (typ A∙) × (typ B∙)
(A∙ ×∙ B∙) .snd .fst = pt A∙
(A∙ ×∙ B∙) .snd .snd = pt B∙

-- composition of pointed maps
_∘∙_ : {A : Pointed ℓA} {B : Pointed ℓB} {C : Pointed ℓC}
       (g : B →∙ C) (f : A →∙ B) → (A →∙ C)
((g , g∙) ∘∙ (f , f∙)) .fst x = g (f  x)
((g , g∙) ∘∙ (f , f∙)) .snd = (cong g f∙) ∙ g∙

-- post composition
post∘∙ : ∀ {ℓX ℓ ℓ'} (X : Pointed ℓX) {A : Pointed ℓ} {B : Pointed ℓ'}
  → (A →∙ B) → ((X →∙ A ∙) →∙ (X →∙ B ∙))
post∘∙ X f .fst g = f ∘∙ g
post∘∙ X f .snd =
  ΣPathP
    ( (funExt λ _ → f .snd)
    , (sym (lUnit (f .snd)) ◁ λ i j → f .snd (i ∨ j)))

-- pointed identity
id∙ : (A : Pointed ℓA) → (A →∙ A)
id∙ A .fst x = x
id∙ A .snd = refl

-- constant pointed map
const∙ : (A : Pointed ℓA) (B : Pointed ℓB) → (A →∙ B)
const∙ _ B .fst _ = B .snd
const∙ _ B .snd = refl

-- left identity law for pointed maps
∘∙-idˡ : {A : Pointed ℓA} {B : Pointed ℓB} (f : A →∙ B) → f ∘∙ id∙ A ≡ f
∘∙-idˡ f = ΣPathP ( refl , (lUnit (f .snd)) ⁻¹ )

-- right identity law for pointed maps
∘∙-idʳ : {A : Pointed ℓA} {B : Pointed ℓB} (f : A →∙ B) → id∙ B ∘∙ f ≡ f
∘∙-idʳ f = ΣPathP ( refl , (rUnit (f .snd)) ⁻¹ )

-- associativity for composition of pointed maps
∘∙-assoc : {A : Pointed ℓA} {B : Pointed ℓB} {C : Pointed ℓC} {D : Pointed ℓD}
           (h : C →∙ D) (g : B →∙ C) (f : A →∙ B)
           → (h ∘∙ g) ∘∙ f ≡ h ∘∙ (g ∘∙ f)
∘∙-assoc (h , h∙) (g , g∙) (f , f∙) = ΣPathP (refl , q)
  where
    q : (cong (h ∘ g) f∙) ∙ (cong h g∙ ∙ h∙) ≡ cong h (cong g f∙ ∙ g∙) ∙ h∙
    q = ( (cong (h ∘ g) f∙) ∙ (cong h g∙ ∙ h∙)
        ≡⟨ refl ⟩
        (cong h (cong g f∙)) ∙ (cong h g∙ ∙ h∙)
        ≡⟨ assoc (cong h (cong g f∙)) (cong h g∙) h∙ ⟩
        (cong h (cong g f∙) ∙ cong h g∙) ∙ h∙
        ≡⟨ cong (λ p → p ∙ h∙) ((cong-∙ h (cong g f∙) g∙) ⁻¹) ⟩
        (cong h (cong g f∙ ∙ g∙) ∙ h∙) ∎ )

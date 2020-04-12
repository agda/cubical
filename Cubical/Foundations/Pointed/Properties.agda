{-# OPTIONS --cubical --safe #-}
module Cubical.Foundations.Pointed.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed.Base
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Structure

open import Cubical.Data.Prod
open import Cubical.Data.Nat
open import Cubical.Data.Sigma

Π∙ : ∀ {ℓ ℓ'} (A : Type ℓ) (B∙ : A → Pointed ℓ') → Pointed (ℓ-max ℓ ℓ')
Π∙ A B∙ = (∀ a → typ (B∙ a)) , (λ a → pt (B∙ a))

Σ∙ : ∀ {ℓ ℓ'} (A∙ : Pointed ℓ) (B∙ : typ A∙ → Pointed ℓ') → Pointed (ℓ-max ℓ ℓ')
Σ∙ A∙ B∙ = (Σ[ a ∈ typ A∙ ] typ (B∙ a)) , (pt A∙ , pt (B∙ (pt A∙)))

_×∙_ : ∀ {ℓ ℓ'} (A∙ : Pointed ℓ) (B∙ : Pointed ℓ') → Pointed (ℓ-max ℓ ℓ')
A∙ ×∙ B∙ = ((typ A∙) × (typ B∙)) , (pt A∙ , pt B∙)

{- composition of pointed maps -}
_∘∙_ : ∀ {ℓA ℓB ℓC} {A : Pointed ℓA} {B : Pointed ℓB} {C : Pointed ℓC}
       (g : B →∙ C) (f : A →∙ B) → (A →∙ C)
(g , g∙) ∘∙ (f , f∙) = (λ x → g (f  x)) , ((cong g f∙) ∙ g∙)

{- pointed identity -}
∙-id : ∀ {ℓA} (A : Pointed ℓA) → (A →∙ A)
∙-id A = ((λ x → x) , refl)

{- left identity law for pointed maps -}
∘∙-idˡ : ∀ {ℓA ℓB} {A : Pointed ℓA} {B : Pointed ℓB} (f : A →∙ B) → f ∘∙ ∙-id A ≡ f
∘∙-idˡ (f , f∙) = ΣPathP ( refl , (lUnit f∙) ⁻¹ )

{- right identity law for pointed maps -}
∘∙-idʳ : ∀ {ℓA ℓB} {A : Pointed ℓA} {B : Pointed ℓB} (f : A →∙ B) → ∙-id B ∘∙ f ≡ f
∘∙-idʳ (f , f∙) = ΣPathP ( refl , (rUnit f∙) ⁻¹ )

{- associativity for composition of pointed maps -}
∘∙-assoc : ∀ {ℓA ℓB ℓC ℓD} {A : Pointed ℓA} {B : Pointed ℓB} {C : Pointed ℓC} {D : Pointed ℓD}
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

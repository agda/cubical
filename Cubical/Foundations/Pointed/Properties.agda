{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Foundations.Pointed.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed.Base
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Data.Sigma

open import Cubical.Structures.Pointed using (pointedSIP)

private
  variable
    ℓ ℓ' ℓA ℓB ℓC ℓD : Level

-- the default pointed Π-type: A is pointed, and B has a base point in the chosen fiber
Π∙ : (A : Pointed ℓ) (B : typ A → Type ℓ') (ptB : B (pt A)) → Type (ℓ-max ℓ ℓ')
Π∙ A B ptB = Σ[ f ∈ ((a : typ A) → B a) ] f (pt A) ≡ ptB

-- the unpointed Π-type becomes a pointed type if the fibers are all pointed
Πᵘ∙ : (A : Type ℓ) (B : A → Pointed ℓ') → Pointed (ℓ-max ℓ ℓ')
Πᵘ∙ A B = (∀ a → typ (B a)) , (λ a → pt (B a))

-- if the base and all fibers are pointed, we have the pointed pointed Π-type
Πᵖ∙ : (A : Pointed ℓ) (B : typ A → Pointed ℓ') → Pointed (ℓ-max ℓ ℓ')
Πᵖ∙ A B = Π∙ A (typ ∘ B) (pt (B (pt A))), ((λ a → pt (B a)) , refl)

-- the default pointed Σ-type is just the Σ-type, but as a pointed type
Σ∙ : (A : Pointed ℓ) (B : typ A → Type ℓ') (ptB : B (pt A)) → Pointed (ℓ-max ℓ ℓ')
Σ∙ A B ptB = (Σ[ a ∈ typ A ] B a) , (pt A , ptB)

-- version if B is a family of pointed types
Σᵖ∙ : (A : Pointed ℓ) (B : typ A → Pointed ℓ') → Pointed (ℓ-max ℓ ℓ')
Σᵖ∙ A B = Σ∙ A (typ ∘ B) (pt (B (pt A)))

_×∙_ : (A∙ : Pointed ℓ) (B∙ : Pointed ℓ') → Pointed (ℓ-max ℓ ℓ')
A∙ ×∙ B∙ = ((typ A∙) × (typ B∙)) , (pt A∙ , pt B∙)

-- composition of pointed maps
_∘∙_ : {A : Pointed ℓA} {B : Pointed ℓB} {C : Pointed ℓC}
       (g : B →∙ C) (f : A →∙ B) → (A →∙ C)
(g , g∙) ∘∙ (f , f∙) = (λ x → g (f  x)) , ((cong g f∙) ∙ g∙)

-- pointed identity
id∙ : (A : Pointed ℓA) → (A →∙ A)
id∙ A = ((λ x → x) , refl)

-- constant pointed map
const∙ : (A : Pointed ℓA) (B : Pointed ℓB) → (A →∙ B)
const∙ _ (_ , b) = (λ _ → b) , refl

-- left identity law for pointed maps
∘∙-idˡ : {A : Pointed ℓA} {B : Pointed ℓB} (f : A →∙ B) → f ∘∙ id∙ A ≡ f
∘∙-idˡ (_ , f∙) = ΣPathP ( refl , (lUnit f∙) ⁻¹ )

-- right identity law for pointed maps
∘∙-idʳ : {A : Pointed ℓA} {B : Pointed ℓB} (f : A →∙ B) → id∙ B ∘∙ f ≡ f
∘∙-idʳ (_ , f∙) = ΣPathP ( refl , (rUnit f∙) ⁻¹ )

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


-- →∙ is a special case of Π∙,
-- but they're not exactly judgementally equal
module _ {A : Pointed ℓ} {B : Pointed ℓ'} where

  B₁ = fst B
  B₂ = snd B

  →∙→Π∙ : (f : A →∙ B) → Π∙ A (λ _ → B₁) B₂
  →∙→Π∙ f = f

  Π∙→→∙ : (f : Π∙ A (λ _ → B₁) B₂) → A →∙ B
  Π∙→→∙ f = f

  →Π∙Iso : Iso (A →∙ B) (Π∙ A (λ _ → B₁) B₂)
  →Π∙Iso = iso (λ f → f) (λ f → f) (λ _ → refl) λ _ → refl


pathToPointedMap : {A B : Pointed ℓ} → A ≡ B → (A →∙ B)
pathToPointedMap {A = A} {B = B} p =  ≃∙To→∙ (equivFun (invEquiv (pointedSIP A B)) p)

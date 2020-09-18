{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Foundations.Pointed.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sigma

open import Cubical.Foundations.Structure
open import Cubical.Foundations.Structure using (typ) public
open import Cubical.Foundations.GroupoidLaws

private
  variable
    ℓ ℓ' : Level

Pointed : (ℓ : Level) → Type (ℓ-suc ℓ)
Pointed ℓ = TypeWithStr ℓ (λ x → x)

pt : ∀ {ℓ} (A∙ : Pointed ℓ) → typ A∙
pt = str

Pointed₀ = Pointed ℓ-zero

{- Pointed functions -}
_→∙_ : ∀{ℓ ℓ'} → (A : Pointed ℓ) (B : Pointed ℓ') → Type (ℓ-max ℓ ℓ')
_→∙_ A B = Σ[ f ∈ (typ A → typ B) ] f (pt A) ≡ pt B

_→∙_∙ : ∀{ℓ ℓ'} → (A : Pointed ℓ) (B : Pointed ℓ') → Pointed (ℓ-max ℓ ℓ')
A →∙ B ∙  = (A →∙ B) , (λ x → pt B) , refl

idfun∙ : ∀ {ℓ} (A : Pointed ℓ) → A →∙ A
idfun∙ A = (λ x → x) , refl

-- Pointed equivalences
_≃∙_ : (A : Pointed ℓ) (B : Pointed ℓ') → Type (ℓ-max ℓ ℓ')
A ≃∙ B = Σ[ (f , p) ∈ A →∙ B ] isEquiv f

≃∙→≃ : {A : Pointed ℓ} {B : Pointed ℓ'}
       (f : A ≃∙ B)
       → typ A ≃ typ B
≃∙→≃ f = fst (fst f) , snd f

idEquiv∙ : (A : Pointed ℓ) → A ≃∙ A
idEquiv∙ (A , ⋆) =
  (idfun∙ (A , ⋆)) ,
  record { equiv-proof = λ a → p a }
    where
      module _ (a : A) where
        p : isContr (Σ[ a' ∈ A ] a' ≡ a)
        p = isContrRespectEquiv (Σ-cong-equiv-snd (λ a₁ → isoToEquiv (iso sym sym (λ _ → refl) λ _ → refl))) (isContrSingl a)

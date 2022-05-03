{-

  Definition of univalent and displayed univalent relations

-}
{-# OPTIONS --safe #-}
module Cubical.Displayed.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport

open import Cubical.Data.Sigma

open import Cubical.Relation.Binary

private
  variable
    ℓ ℓA ℓA' ℓ≅A ℓB ℓB' ℓ≅B ℓC ℓ≅C : Level

record UARel (A : Type ℓA) (ℓ≅A : Level) : Type (ℓ-max ℓA (ℓ-suc ℓ≅A)) where
  no-eta-equality
  constructor uarel
  field
    _≅_ : A → A → Type ℓ≅A
    ua : (a a' : A) → (a ≅ a') ≃ (a ≡ a')

  uaIso : (a a' : A) → Iso (a ≅ a') (a ≡ a')
  uaIso a a' = equivToIso (ua a a')

  ≅→≡ : {a a' : A} (p : a ≅ a') → a ≡ a'
  ≅→≡ {a} {a'} = Iso.fun (uaIso a a')
  ≡→≅ : {a a' : A} (p : a ≡ a') → a ≅ a'
  ≡→≅ {a} {a'} = Iso.inv (uaIso a a')

  ρ : (a : A) → a ≅ a
  ρ a = ≡→≅ refl

open BinaryRelation

-- another constructor for UARel using contractibility of relational singletons
make-𝒮 : {A : Type ℓA} {_≅_ : A → A → Type ℓ≅A}
          (ρ : isRefl _≅_) (contrTotal : contrRelSingl _≅_) → UARel A ℓ≅A
UARel._≅_ (make-𝒮 {_≅_ = _≅_} _ _) = _≅_
UARel.ua (make-𝒮 {_≅_ = _≅_} ρ c) = contrRelSingl→isUnivalent _≅_ ρ c

record DUARel {A : Type ℓA} (𝒮-A : UARel A ℓ≅A)
              (B : A → Type ℓB) (ℓ≅B : Level) : Type (ℓ-max (ℓ-max ℓA ℓB) (ℓ-max ℓ≅A (ℓ-suc ℓ≅B))) where
  no-eta-equality
  constructor duarel
  open UARel 𝒮-A

  field
    _≅ᴰ⟨_⟩_ : {a a' : A} → B a → a ≅ a' → B a' → Type ℓ≅B
    uaᴰ : {a a' : A} (b : B a) (p : a ≅ a') (b' : B a') → (b ≅ᴰ⟨ p ⟩ b') ≃ PathP (λ i → B (≅→≡ p i)) b b'

  fiberRel : (a : A) → Rel (B a) (B a) ℓ≅B
  fiberRel a = _≅ᴰ⟨ ρ a ⟩_

  uaᴰρ : {a : A} (b b' : B a) → b ≅ᴰ⟨ ρ a ⟩ b' ≃ (b ≡ b')
  uaᴰρ {a} b b' =
    compEquiv
      (uaᴰ b (ρ _) b')
      (substEquiv (λ q → PathP (λ i → B (q i)) b b') (secEq (ua a a) refl))

  ρᴰ : {a : A} → (b : B a) → b ≅ᴰ⟨ ρ a ⟩ b
  ρᴰ {a} b = invEq (uaᴰρ b b) refl


-- total UARel induced by a DUARel

module _ {A : Type ℓA} {𝒮-A : UARel A ℓ≅A}
  {B : A → Type ℓB} {ℓ≅B : Level}
  (𝒮ᴰ-B : DUARel 𝒮-A B ℓ≅B)
  where

  open UARel 𝒮-A
  open DUARel 𝒮ᴰ-B

  ∫ : UARel (Σ A B) (ℓ-max ℓ≅A ℓ≅B)
  UARel._≅_ ∫ (a , b) (a' , b') = Σ[ p ∈ a ≅ a' ] (b ≅ᴰ⟨ p ⟩ b')
  UARel.ua ∫ (a , b) (a' , b') =
    compEquiv
      (Σ-cong-equiv (ua a a') (λ p → uaᴰ b p b'))
      ΣPath≃PathΣ


{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Displayed.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport

open import Cubical.Functions.FunExtEquiv

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
  ρ : (a : A) → a ≅ a
  ρ a = invEq (ua a a) refl
  ≅→≡ : {a a' : A} (p : a ≅ a') → a ≡ a'
  ≅→≡ {a} {a'} p = equivFun (ua a a') p
  ≡→≅ : {a a' : A} (p : a ≡ a') → a ≅ a'
  ≡→≅ {a} {a'} p = equivFun (invEquiv (ua a a')) p

open BinaryRelation

-- another constructor for UARel using contractibility of relational singletons
make-𝒮 : {A : Type ℓA} {ℓ≅A : Level} {_≅_ : A → A → Type ℓ≅A}
          (ρ : isRefl _≅_) (contrTotal : contrRelSingl _≅_) → UARel A ℓ≅A
UARel._≅_ (make-𝒮 {_≅_ = _≅_} _ _) = _≅_
UARel.ua (make-𝒮 {_≅_ = _≅_} ρ c) = contrRelSingl→isUnivalent _≅_ ρ c

record DUARel {A : Type ℓA} {ℓ≅A : Level} (𝒮-A : UARel A ℓ≅A)
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
      (substEquiv (λ q → PathP (λ i → B (q i)) b b') (retEq (ua a a) refl))

  ρᴰ : {a : A} → (b : B a) → b ≅ᴰ⟨ ρ a ⟩ b
  ρᴰ {a} b = invEq (uaᴰρ b b) refl

-- Not sure if useful for this definition
{-
make-𝒮ᴰ : {A : Type ℓA} {𝒮-A : UARel A ℓ≅A}
          {B : A → Type ℓB}
          (_≅ᴰ⟨_⟩_ : {a a' : A} → B a → UARel._≅_ 𝒮-A a a' → B a' → Type ℓ≅B)
          (ρᴰ : {a : A} → isRefl _≅ᴰ⟨ UARel.ρ 𝒮-A a ⟩_)
          (contrTotal : (a : A) → contrRelSingl _≅ᴰ⟨ UARel.ρ 𝒮-A a ⟩_)
          → DUARel 𝒮-A B ℓ≅B
DUARel._≅ᴰ⟨_⟩_ (make-𝒮ᴰ _≅ᴰ⟨_⟩_ ρᴰ contrTotal) = _≅ᴰ⟨_⟩_
DUARel.uaᴰ (make-𝒮ᴰ {𝒮-A = 𝒮-A} _≅ᴰ⟨_⟩_ ρᴰ contrTotal) {a} b b'
  = contrRelSingl→isUnivalent (_≅ᴰ⟨ UARel.ρ 𝒮-A a ⟩_) (ρᴰ {a}) (contrTotal a) b b'
-}

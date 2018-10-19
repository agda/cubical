{-

This file contains:

- Definitions of fibers, isContr and equivalences

- Glue types

- The identity equivalence and the ua constant


It should *not* depend on the Agda standard library.

 -}
{-# OPTIONS --cubical #-}
module Cubical.Glue where

open import Cubical.Prelude

fiber : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) (y : B) → Set (ℓ-max ℓ ℓ')
fiber {A = A} f y = Σ[ x ∈ A ] y ≡ f x

isContr : {ℓ : Level} (A : Set ℓ) → Set ℓ
isContr A = Σ[ x ∈ A ] (∀ y → x ≡ y)

module _ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') where
  contrFibers : (A → B) → Set (ℓ-max ℓ ℓ')
  contrFibers f = (y : B) → isContr (fiber f y)

  record isEquiv (f : A → B) : Set (ℓ-max ℓ ℓ') where
    field
      equiv-proof : contrFibers f
  open isEquiv public

  infix 4 _≃_
  _≃_ = Σ _ isEquiv

equivFun : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → A ≃ B → A → B
equivFun e = fst e

-- TODO: Maybe change the internal definition of equivalence?
{-# BUILTIN EQUIV _≃_ #-}
{-# BUILTIN EQUIVFUN  equivFun #-}

-- I don't know why this should be a module...
module GluePrims where
  primitive
    primGlue    : ∀ {ℓ ℓ'} (A : Set ℓ) {φ : I}
      → (T : Partial (Set ℓ') φ) → (e : PartialP φ (λ o → T o ≃ A))
      → Set ℓ'
    prim^glue   : ∀ {ℓ ℓ'} {A : Set ℓ} {φ : I}
      → {T : Partial (Set ℓ') φ} → {e : PartialP φ (λ o → T o ≃ A)}
      → PartialP φ T → A → primGlue A T e
    prim^unglue : ∀ {ℓ ℓ'} {A : Set ℓ} {φ : I}
      → {T : Partial (Set ℓ') φ} → {e : PartialP φ (λ o → T o ≃ A)}
      → primGlue A T e → A

open GluePrims public
  renaming ( primGlue to Glue
           ; prim^glue to glue
           ; prim^unglue to unglue)

-- The identity equivalence
idEquiv : ∀ {ℓ} → (A : Set ℓ) → A ≃ A
idEquiv A = (λ a → a) , (λ { .equiv-proof y → (y , refl) , \ z → contrSingl (z .snd)  })

-- The ua constant
ua : ∀ {ℓ} {A B : Set ℓ} → A ≃ B → A ≡ B
ua {_} {A} {B} e i =
  Glue B (λ {(i = i0) → _ ; (i = i1) → _}) -- Why is this argument needed?
         (λ {(i = i0) → e ; (i = i1) → idEquiv B})


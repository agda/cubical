{-# OPTIONS --safe #-}

module Cubical.HITs.FreeComMonoids.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

private variable
  ℓ : Level
  A : Type ℓ

data FreeComMonoid (A : Type ℓ) : Type ℓ where
  ⟦_⟧       : A → FreeComMonoid A
  ε         : FreeComMonoid A
  _·_       : FreeComMonoid A → FreeComMonoid A → FreeComMonoid A
  comm      : ∀ x y   → x · y ≡ y · x
  identityᵣ : ∀ x     → x · ε ≡ x
  identityₗ : ∀ x     → ε · x ≡ x
  assoc     : ∀ x y z → x · (y · z) ≡ (x · y) · z
  trunc     : isSet (FreeComMonoid A)

module Elim {ℓ'} {B : FreeComMonoid A → Type ℓ'}
  (⟦_⟧*       : (x : A) → B ⟦ x ⟧)
  (ε*         : B ε)
  (_·*_       : ∀ {x y}   → B x → B y → B (x · y))
  (comm*      : ∀ {x y}   → (xs : B x) (ys : B y)
    → PathP (λ i → B (comm x y i)) (xs ·* ys) (ys ·* xs))
  (identityᵣ* : ∀ {x}     → (xs : B x)
    → PathP (λ i → B (identityᵣ x i)) (xs ·* ε*) xs)
  (identityₗ* : ∀ {x}     → (xs : B x)
    → PathP (λ i → B (identityₗ x i)) (ε* ·* xs) xs)
  (assoc*     : ∀ {x y z} → (xs : B x) (ys : B y) (zs : B z)
    → PathP (λ i → B (assoc x y z i)) (xs ·* (ys ·* zs)) ((xs ·* ys) ·* zs))
  (trunc*     : ∀ xs → isSet (B xs)) where

  f : (xs : FreeComMonoid A) → B xs
  f ⟦ x ⟧ = ⟦ x ⟧*
  f ε = ε*
  f (xs · ys) = f xs ·* f ys
  f (comm xs ys i) = comm* (f xs) (f ys) i
  f (identityᵣ xs i) = identityᵣ* (f xs) i
  f (identityₗ xs i) = identityₗ* (f xs) i
  f (assoc xs ys zs i) = assoc* (f xs) (f ys) (f zs) i
  f (trunc xs ys p q i j) = isOfHLevel→isOfHLevelDep 2 trunc*  (f xs) (f ys)
    (cong f p) (cong f q) (trunc xs ys p q) i j

module ElimProp {ℓ'} {B : FreeComMonoid A → Type ℓ'}
  (BProp : {xs : FreeComMonoid A} → isProp (B xs))
  (⟦_⟧*       : (x : A) → B ⟦ x ⟧)
  (ε*         : B ε)
  (_·*_       : ∀ {x y}   → B x → B y → B (x · y)) where

  f : (xs : FreeComMonoid A) → B xs
  f = Elim.f ⟦_⟧* ε* _·*_
    (λ {x y} xs ys → toPathP (BProp (transport (λ i → B (comm x y i)) (xs ·* ys)) (ys ·* xs)))
    (λ {x} xs → toPathP (BProp (transport (λ i → B (identityᵣ x i)) (xs ·* ε*)) xs))
    (λ {x} xs → toPathP (BProp (transport (λ i → B (identityₗ x i)) (ε* ·* xs)) xs))
    (λ {x y z} xs ys zs → toPathP (BProp (transport (λ i → B (assoc x y z i)) (xs ·* (ys ·* zs))) ((xs ·* ys) ·* zs)))
    (λ _ → (isProp→isSet BProp))

module Rec {ℓ'} {B : Type ℓ'} (BType : isSet B)
  (⟦_⟧*       : (x : A) → B)
  (ε*         : B)
  (_·*_       : B → B → B)
  (comm*      : (x y : B) → x ·* y ≡ y ·* x)
  (identityᵣ* : (x : B) → x ·* ε* ≡ x)
  (identityₗ* : (x : B) → ε* ·* x ≡ x)
  (assoc*     : (x y z : B) → x ·* (y ·* z) ≡ (x ·* y) ·* z)
  where

  f : FreeComMonoid A → B
  f = Elim.f ⟦_⟧* ε* _·*_ comm* identityᵣ* identityₗ* assoc* (const BType)

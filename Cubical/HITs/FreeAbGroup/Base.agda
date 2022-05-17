{-# OPTIONS --safe #-}
module Cubical.HITs.FreeAbGroup.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

infixl 7 _·_
infix 20 _⁻¹

private variable
  ℓ ℓ' : Level
  A : Type ℓ

data FreeAbGroup (A : Type ℓ) : Type ℓ where
  ⟦_⟧       : A → FreeAbGroup A
  ε         : FreeAbGroup A
  _·_       : FreeAbGroup A → FreeAbGroup A → FreeAbGroup A
  _⁻¹       : FreeAbGroup A → FreeAbGroup A
  assoc     : ∀ x y z → x · (y · z) ≡ (x · y) · z
  comm      : ∀ x y   → x · y       ≡ y · x
  identityᵣ : ∀ x     → x · ε       ≡ x
  invᵣ      : ∀ x     → x · x ⁻¹    ≡ ε
  trunc     : isSet (FreeAbGroup A)

module Elim {B : FreeAbGroup A → Type ℓ'}
  (⟦_⟧*       : (x : A) → B ⟦ x ⟧)
  (ε*         : B ε)
  (_·*_       : ∀ {x y}   → B x → B y → B (x · y))
  (_⁻¹*       : ∀ {x}     → B x → B (x ⁻¹))
  (assoc*     : ∀ {x y z} → (xs : B x) (ys : B y) (zs : B z)
    → PathP (λ i → B (assoc x y z i)) (xs ·* (ys ·* zs)) ((xs ·* ys) ·* zs))
  (comm*      : ∀ {x y}   → (xs : B x) (ys : B y)
    → PathP (λ i → B (comm x y i)) (xs ·* ys) (ys ·* xs))
  (identityᵣ* : ∀ {x}     → (xs : B x)
    → PathP (λ i → B (identityᵣ x i)) (xs ·* ε*) xs)
  (invᵣ* : ∀ {x} → (xs : B x)
    → PathP (λ i → B (invᵣ x i)) (xs ·* (xs ⁻¹*)) ε*)
  (trunc*     : ∀ xs → isSet (B xs)) where

  f : (xs : FreeAbGroup A) → B xs
  f ⟦ x ⟧ = ⟦ x ⟧*
  f ε = ε*
  f (xs · ys) = f xs ·* f ys
  f (xs ⁻¹) = f xs ⁻¹*
  f (assoc xs ys zs i) = assoc* (f xs) (f ys) (f zs) i
  f (comm xs ys i) = comm* (f xs) (f ys) i
  f (identityᵣ xs i) = identityᵣ* (f xs) i
  f (invᵣ xs i) = invᵣ* (f xs) i
  f (trunc xs ys p q i j) = isOfHLevel→isOfHLevelDep 2 trunc*  (f xs) (f ys)
    (cong f p) (cong f q) (trunc xs ys p q) i j

module ElimProp {B : FreeAbGroup A → Type ℓ'}
  (BProp : {xs : FreeAbGroup A} → isProp (B xs))
  (⟦_⟧*       : (x : A) → B ⟦ x ⟧)
  (ε*         : B ε)
  (_·*_       : ∀ {x y}   → B x → B y → B (x · y))
  (_⁻¹*       : ∀ {x}     → B x → B (x ⁻¹)) where

  f : (xs : FreeAbGroup A) → B xs
  f = Elim.f ⟦_⟧* ε* _·*_ _⁻¹*
    (λ {x y z} xs ys zs → toPathP (BProp (transport (λ i → B (assoc x y z i)) (xs ·* (ys ·* zs))) ((xs ·* ys) ·* zs)))
    (λ {x y} xs ys → toPathP (BProp (transport (λ i → B (comm x y i)) (xs ·* ys)) (ys ·* xs)))
    (λ {x} xs → toPathP (BProp (transport (λ i → B (identityᵣ x i)) (xs ·* ε*)) xs))
    (λ {x} xs → toPathP (BProp (transport (λ i → B (invᵣ x i)) (xs ·* (xs ⁻¹*))) ε*))
    (λ _ → (isProp→isSet BProp))

module Rec {B : Type ℓ'} (BType : isSet B)
  (⟦_⟧*       : (x : A) → B)
  (ε*         : B)
  (_·*_       : B → B → B)
  (_⁻¹*       : B → B)
  (assoc*     : (x y z : B) → x ·* (y ·* z) ≡ (x ·* y) ·* z)
  (comm*      : (x y : B)   → x ·* y        ≡ y ·* x)
  (identityᵣ* : (x : B)     → x ·* ε*       ≡ x)
  (invᵣ*      : (x : B)     → x ·* (x ⁻¹*)  ≡ ε*)
  where

  f : FreeAbGroup A → B
  f = Elim.f ⟦_⟧* ε* _·*_ _⁻¹* assoc* comm* identityᵣ* invᵣ* (const BType)

{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Homotopy.WhiteheadProducts.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Pointed

open import Cubical.Data.Nat

open import Cubical.HITs.Susp renaming (toSusp to σ)
open import Cubical.HITs.Pushout
open import Cubical.HITs.Sn
open import Cubical.HITs.Sn.Multiplication
open import Cubical.HITs.Join
open import Cubical.HITs.Wedge
open import Cubical.HITs.SetTruncation

open import Cubical.Homotopy.Group.Base
open import Cubical.Homotopy.Loopspace

open Iso

-- Whitehead product (main definition)
[_∣_]-pre : ∀ {ℓ} {X : Pointed ℓ} {n m : ℕ}
       → (S₊∙ (suc n) →∙ X)
       → (S₊∙ (suc m) →∙ X)
       → join∙ (S₊∙ n) (S₊∙ m) →∙ X
fst ([_∣_]-pre {X = X} {n = n} {m = m} f g) (inl x) = pt X
fst ([_∣_]-pre {X = X} {n = n} {m = m} f g) (inr x) = pt X
fst ([_∣_]-pre {n = n} {m = m} f g) (push a b i) =
  (Ω→ g .fst (σS b) ∙ Ω→ f .fst (σS a)) i
snd ([_∣_]-pre {n = n} {m = m} f g) = refl

[_∣_] : ∀ {ℓ} {X : Pointed ℓ} {n m : ℕ}
       → (S₊∙ (suc n) →∙ X)
       → (S₊∙ (suc m) →∙ X)
       → S₊∙ (suc (n + m)) →∙ X
[_∣_] {n = n} {m = m} f g =
  [ f ∣ g ]-pre ∘∙ (sphere→Join n m , IsoSphereJoin⁻Pres∙ n m)

-- Homotopy group version
[_∣_]π' : ∀ {ℓ} {X : Pointed ℓ} {n m : ℕ}
       → π' (suc n) X → π' (suc m) X
       → π' (suc (n + m)) X
[_∣_]π' = elim2 (λ _ _ → squash₂) λ f g → ∣ [ f ∣ g ] ∣₂

-- Whitehead product (as a composition)
joinTo⋁ : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'}
 → join (typ A) (typ B)
 → (Susp (typ A) , north) ⋁ (Susp (typ B) , north)
joinTo⋁ (inl x) = inr north
joinTo⋁ (inr x) = inl north
joinTo⋁ {A = A} {B = B} (push a b i) =
     ((λ i → inr (σ B b i))
  ∙∙ sym (push tt)
  ∙∙ λ i → inl (σ A a i)) i

[_∣_]comp : ∀ {ℓ} {X : Pointed ℓ} {n m : ℕ}
       → (S₊∙ (suc n) →∙ X)
       → (S₊∙ (suc m) →∙ X)
       → S₊∙ (suc (n + m)) →∙ X
[_∣_]comp {n = n} {m = m} f g =
    (((f ∘∙ (inv (IsoSucSphereSusp n) , IsoSucSphereSusp∙ n))
  ∨→ (g ∘∙ (inv (IsoSucSphereSusp m) , IsoSucSphereSusp∙ m))
    , cong (fst f) (IsoSucSphereSusp∙ n) ∙ snd f)
  ∘∙ ((joinTo⋁ {A = S₊∙ n} {B = S₊∙ m} , sym (push tt))))
  ∘∙ (inv (IsoSphereJoin n m) , IsoSphereJoin⁻Pres∙ n m)

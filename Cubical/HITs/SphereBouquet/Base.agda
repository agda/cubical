
module Cubical.HITs.SphereBouquet.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed

open import Cubical.Data.Nat
open import Cubical.Data.Fin.Inductive

open import Cubical.HITs.Wedge
open import Cubical.HITs.Sn

SphereBouquet : ∀ {ℓ} (n : ℕ) (A : Type ℓ) → Type ℓ
SphereBouquet n A = ⋁gen A λ a → S₊∙ n

SphereBouquet∙ : ∀ {ℓ} (n : ℕ) (A : Type ℓ) → Pointed ℓ
SphereBouquet∙ n A = ⋁gen∙ A λ a → S₊∙ n

FinSphereBouquetMap : (c1 c2 : ℕ) (n : ℕ) → Type
FinSphereBouquetMap c1 c2 n =
  SphereBouquet (suc n) (Fin c1) → SphereBouquet (suc n) (Fin c2)

FinSphereBouquetMap∙ : (c1 c2 : ℕ) (n : ℕ) → Type
FinSphereBouquetMap∙ c1 c2 n =
  SphereBouquet∙ (suc n) (Fin c1) →∙ SphereBouquet∙ (suc n) (Fin c2)

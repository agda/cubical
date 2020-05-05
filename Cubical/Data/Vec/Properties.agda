{-# OPTIONS --cubical --safe #-}
module Cubical.Data.Vec.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat
open import Cubical.Data.Vec.Base
open import Cubical.Data.FinData
open import Cubical.Relation.Nullary

private
  variable
    ℓ : Level


-- This is really cool!
-- Compare with: https://github.com/agda/agda-stdlib/blob/master/src/Data/Vec/Properties/WithK.agda#L32
++-assoc : ∀ {m n k} {A : Type ℓ} (xs : Vec A m) (ys : Vec A n) (zs : Vec A k) →
           PathP (λ i → Vec A (+-assoc m n k (~ i))) ((xs ++ ys) ++ zs) (xs ++ ys ++ zs)
++-assoc {m = zero} [] ys zs = refl
++-assoc {m = suc m} (x ∷ xs) ys zs i = x ∷ ++-assoc xs ys zs i


-- Equivalence between Fin n → A and Vec A n

FinVec : (A : Type ℓ) (n : ℕ) → Type ℓ
FinVec A n = Fin n → A

FinVec→Vec : (A : Type ℓ) (n : ℕ) → FinVec A n → Vec A n
FinVec→Vec A zero xs = []
FinVec→Vec A (suc n) xs = xs zero ∷ FinVec→Vec A n (λ x → xs (suc x))

Vec→FinVec : (A : Type ℓ) (n : ℕ) → Vec A n → FinVec A n
Vec→FinVec A n xs f = lookup f xs

FinVec→Vec→FinVec : (A : Type ℓ) (n : ℕ) (xs : FinVec A n) → Vec→FinVec A n (FinVec→Vec A n xs) ≡ xs
FinVec→Vec→FinVec A zero xs = funExt λ f → ⊥.rec (¬Fin0 f)
FinVec→Vec→FinVec A (suc n) xs = funExt goal
  where
  goal : (f : Fin (suc n))
       → Vec→FinVec A (suc n) (xs zero ∷ FinVec→Vec A n (λ x₁ → xs (suc x₁))) f ≡ xs f
  goal zero = refl
  goal (suc f) i = FinVec→Vec→FinVec A n (λ x → xs (suc x)) i f

Vec→FinVec→Vec : (A : Type ℓ) (n : ℕ) (xs : Vec A n) → FinVec→Vec A n (Vec→FinVec A n xs) ≡ xs
Vec→FinVec→Vec A zero [] = refl
Vec→FinVec→Vec A (suc n) (x ∷ xs) = λ i → x ∷ Vec→FinVec→Vec A n xs i

FinVecIsoVec : (A : Type ℓ) (n : ℕ) → Iso (FinVec A n) (Vec A n)
FinVecIsoVec A n = iso (FinVec→Vec A n) (Vec→FinVec A n) (Vec→FinVec→Vec A n) (FinVec→Vec→FinVec A n)

FinVec≃Vec : (A : Type ℓ) (n : ℕ) → FinVec A n ≃ Vec A n
FinVec≃Vec A n = isoToEquiv (FinVecIsoVec A n)

FinVec≡Vec : (A : Type ℓ) (n : ℕ) → FinVec A n ≡ Vec A n
FinVec≡Vec A n = ua (FinVec≃Vec A n)


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
    A : Type ℓ


-- This is really cool!
-- Compare with: https://github.com/agda/agda-stdlib/blob/master/src/Data/Vec/Properties/WithK.agda#L32
++-assoc : ∀ {m n k} (xs : Vec A m) (ys : Vec A n) (zs : Vec A k) →
           PathP (λ i → Vec A (+-assoc m n k (~ i))) ((xs ++ ys) ++ zs) (xs ++ ys ++ zs)
++-assoc {m = zero} [] ys zs = refl
++-assoc {m = suc m} (x ∷ xs) ys zs i = x ∷ ++-assoc xs ys zs i


-- Equivalence between Fin n → A and Vec A n

FinVec : (A : Type ℓ) (n : ℕ) → Type ℓ
FinVec A n = Fin n → A

FinVec→Vec : {n : ℕ} → FinVec A n → Vec A n
FinVec→Vec {n = zero}  xs = []
FinVec→Vec {n = suc _} xs = xs zero ∷ FinVec→Vec (λ x → xs (suc x))

Vec→FinVec : {n : ℕ} → Vec A n → FinVec A n
Vec→FinVec xs f = lookup f xs

FinVec→Vec→FinVec : {n : ℕ} (xs : FinVec A n) → Vec→FinVec (FinVec→Vec xs) ≡ xs
FinVec→Vec→FinVec {n = zero} xs = funExt λ f → ⊥.rec (¬Fin0 f)
FinVec→Vec→FinVec {n = suc n} xs = funExt goal
  where
  goal : (f : Fin (suc n))
       → Vec→FinVec (xs zero ∷ FinVec→Vec (λ x → xs (suc x))) f ≡ xs f
  goal zero = refl
  goal (suc f) i = FinVec→Vec→FinVec (λ x → xs (suc x)) i f

Vec→FinVec→Vec : {n : ℕ} (xs : Vec A n) → FinVec→Vec (Vec→FinVec xs) ≡ xs
Vec→FinVec→Vec {n = zero}  [] = refl
Vec→FinVec→Vec {n = suc n} (x ∷ xs) i = x ∷ Vec→FinVec→Vec xs i

FinVecIsoVec : (n : ℕ) → Iso (FinVec A n) (Vec A n)
FinVecIsoVec n = iso FinVec→Vec Vec→FinVec Vec→FinVec→Vec FinVec→Vec→FinVec

FinVec≃Vec : (n : ℕ) → FinVec A n ≃ Vec A n
FinVec≃Vec n = isoToEquiv (FinVecIsoVec n)

FinVec≡Vec : (n : ℕ) → FinVec A n ≡ Vec A n
FinVec≡Vec n = ua (FinVec≃Vec n)

isContrVec0 : isContr (Vec A 0)
isContrVec0 = [] , λ { [] → refl }

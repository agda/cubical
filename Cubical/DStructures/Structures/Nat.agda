{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.DStructures.Structures.Nat where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Functions.FunExtEquiv

open import Cubical.Homotopy.Base

open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Empty
open import Cubical.Data.Unit

open import Cubical.Relation.Binary

open import Cubical.DStructures.Base

private
  variable
    ℓA ℓ≅A : Level

-- observational equality on ℕ
ℕ-≅ : ℕ → ℕ → Type ℓ-zero
ℕ-≅ 0 0 = Unit
ℕ-≅ 0 (suc _) = ⊥
ℕ-≅ (suc _) 0 = ⊥
ℕ-≅ (suc n) (suc m) = ℕ-≅ n m

-- observational equality is reflexive
ℕ-≅-ρ : isRefl ℕ-≅
ℕ-≅-ρ 0 = tt
ℕ-≅-ρ (suc n) = ℕ-≅-ρ n

-- observational equality implies identity
ℕ-≅→≡ : {n m : ℕ} → ℕ-≅ n m → n ≡ m
ℕ-≅→≡ {0} {0} p = refl
ℕ-≅→≡ {0} {suc _} p = rec p
ℕ-≅→≡ {suc _} {0} p = rec p
ℕ-≅→≡ {suc n} {suc m} p = cong suc (ℕ-≅→≡ {n} {m} p)

-- observational equality is prop-valued
ℕ-≅-prop : (n m : ℕ) → isProp (ℕ-≅ n m)
ℕ-≅-prop 0 0 = isContr→isProp isContrUnit
ℕ-≅-prop 0 (suc _) = isProp⊥
ℕ-≅-prop (suc _) 0 = isProp⊥
ℕ-≅-prop (suc n) (suc m) = ℕ-≅-prop n m

-- This module contains the first half of the proof of
-- theorem 10.2.3 of Egbert Rijkes Intro to Hott
-- TODO: privatize
module _ {A : Type ℓA}
         (_≅_ : A → A → Type ℓ≅A)
         (ρ : (a : A) → a ≅ a)
         (prop : (a a' : A) → isProp (a ≅ a'))
         (f : (a a' : A) → (a ≅ a') → a ≡ a')
 where
    module _ (a : A) where
      φ : (a' : A) (p : a ≡ a') → a ≅ a'
      φ a' p = J (λ b q → a ≅ b) (ρ a) p

      tot-f : Σ[ a' ∈ A ] a ≅ a' → singl a
      tot-f (a' , p) = a' , f a a' p

      tot-φ : singl a → Σ[ a' ∈ A ] a ≅ a'
      tot-φ (a' , p) = a' , (φ a' p)

      ret-f-φ : (a' : A) → retract (f a a') (φ a')
      ret-f-φ a' p = prop a a' (φ a' (f a a' p)) p

      retract-totf-totφ : retract tot-f tot-φ
      retract-totf-totφ (a' , p) = ΣPathP (refl , ret-f-φ a' p)

      contr-singl-≅ : isContr (Σ[ a' ∈ A ] a ≅ a')
      contr-singl-≅ = isContrRetract tot-f tot-φ retract-totf-totφ (isContrSingl a)


ℕ-≅-contrSingl : (n : ℕ) → isContr (Σ[ m ∈ ℕ ] ℕ-≅ n m)
ℕ-≅-contrSingl n = contr-singl-≅ ℕ-≅ ℕ-≅-ρ ℕ-≅-prop (λ m m' → ℕ-≅→≡ {m} {m'}) n

𝒮-Nat : URGStr ℕ ℓ-zero
𝒮-Nat = make-𝒮 {_≅_ = ℕ-≅} ℕ-≅-ρ ℕ-≅-contrSingl

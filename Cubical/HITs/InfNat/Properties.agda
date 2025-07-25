{-# OPTIONS --no-exact-split #-}

module Cubical.HITs.InfNat.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Maybe
open import Cubical.Data.Nat

open import Cubical.HITs.InfNat.Base
import Cubical.Data.InfNat as Coprod

ℕ+∞→Cℕ+∞ : ℕ+∞ → Coprod.ℕ+∞
ℕ+∞→Cℕ+∞ zero = Coprod.zero
ℕ+∞→Cℕ+∞ (suc n) = Coprod.suc (ℕ+∞→Cℕ+∞ n)
ℕ+∞→Cℕ+∞ ∞ = Coprod.∞
ℕ+∞→Cℕ+∞ (suc-inf i) = Coprod.∞

ℕ→ℕ+∞ : ℕ → ℕ+∞
ℕ→ℕ+∞ zero = zero
ℕ→ℕ+∞ (suc n) = suc (ℕ→ℕ+∞ n)

Cℕ+∞→ℕ+∞ : Coprod.ℕ+∞ → ℕ+∞
Cℕ+∞→ℕ+∞ Coprod.∞ = ∞
Cℕ+∞→ℕ+∞ (Coprod.fin n) = ℕ→ℕ+∞ n

ℕ→ℕ+∞→Cℕ+∞ : ∀ n → ℕ+∞→Cℕ+∞ (ℕ→ℕ+∞ n) ≡ Coprod.fin n
ℕ→ℕ+∞→Cℕ+∞ zero = refl
ℕ→ℕ+∞→Cℕ+∞ (suc n) = cong Coprod.suc (ℕ→ℕ+∞→Cℕ+∞ n)

Cℕ+∞→ℕ+∞→Cℕ+∞ : ∀ n → ℕ+∞→Cℕ+∞ (Cℕ+∞→ℕ+∞ n) ≡ n
Cℕ+∞→ℕ+∞→Cℕ+∞ Coprod.∞ = refl
Cℕ+∞→ℕ+∞→Cℕ+∞ (Coprod.fin n) = ℕ→ℕ+∞→Cℕ+∞ n

suc-hom : ∀ n → Cℕ+∞→ℕ+∞ (Coprod.suc n) ≡ suc (Cℕ+∞→ℕ+∞ n)
suc-hom Coprod.∞ = suc-inf
suc-hom (Coprod.fin x) = refl

ℕ+∞→Cℕ+∞→ℕ+∞ : ∀ n → Cℕ+∞→ℕ+∞ (ℕ+∞→Cℕ+∞ n) ≡ n
ℕ+∞→Cℕ+∞→ℕ+∞ zero = refl
ℕ+∞→Cℕ+∞→ℕ+∞ ∞ = refl
ℕ+∞→Cℕ+∞→ℕ+∞ (suc n) = suc-hom (ℕ+∞→Cℕ+∞ n) ∙ cong suc (ℕ+∞→Cℕ+∞→ℕ+∞ n)
ℕ+∞→Cℕ+∞→ℕ+∞ (suc-inf i) = lemma i
  where
  lemma : (λ i → ∞ ≡ suc-inf i) [ refl ≡ suc-inf ∙ refl ]
  lemma i j = hcomp (λ k → λ
    { (i = i0) → ∞
    ; (i = i1) → compPath-filler suc-inf refl k j
    ; (j = i0) → ∞
    ; (j = i1) → suc-inf i
    }) (suc-inf (i ∧ j))

open Iso

ℕ+∞⇔Cℕ+∞ : Iso ℕ+∞ Coprod.ℕ+∞
ℕ+∞⇔Cℕ+∞ .fun = ℕ+∞→Cℕ+∞
ℕ+∞⇔Cℕ+∞ .inv = Cℕ+∞→ℕ+∞
ℕ+∞⇔Cℕ+∞ .leftInv = ℕ+∞→Cℕ+∞→ℕ+∞
ℕ+∞⇔Cℕ+∞ .rightInv = Cℕ+∞→ℕ+∞→Cℕ+∞

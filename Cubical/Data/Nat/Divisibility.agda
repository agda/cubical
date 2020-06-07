{-# OPTIONS --cubical --safe #-}
module Cubical.Data.Nat.Divisibility where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥

open import Cubical.HITs.PropositionalTruncation as PropTrunc

open import Cubical.Data.Nat.Base
open import Cubical.Data.Nat.Properties
open import Cubical.Data.Nat.Order

private
  variable
    l m n : ℕ

_∣_ : ℕ → ℕ → Type₀
m ∣ n = ∃[ c ∈ ℕ ] c * m ≡ n

isProp∣ : isProp (m ∣ n)
isProp∣ = squash

prediv : ℕ → ℕ → Type₀
prediv m n = Σ[ c ∈ ℕ ] c * m ≡ n

-- an alternate definition of m ∣ n that doesn't use truncation

_∣'_ : ℕ → ℕ → Type₀
zero  ∣' n = zero ≡ n
suc m ∣' n = Σ[ c ∈ ℕ ] c * suc m ≡ n

isProp∣' : isProp (m ∣' n)
isProp∣' {zero} {n} = isSetℕ _ _
isProp∣' {suc m} {n} (c₁ , p₁) (c₂ , p₂) =
  Σ≡Prop (λ _ → isSetℕ _ _) (inj-*sm {c₁} {m} {c₂} (p₁ ∙ sym p₂))

∣≃∣' : (m ∣ n) ≃ (m ∣' n)
∣≃∣' {zero} = PropEquiv→Equiv isProp∣ isProp∣'
                              (PropTrunc.rec (isSetℕ _ _) λ { (c , p) → 0≡m*0 c ∙ p })
                              (λ p → ∣ zero , p ∣)
∣≃∣' {suc m} = propTruncIdempotent≃ isProp∣'

∣-untrunc : m ∣ n → Σ[ c ∈ ℕ ] c * m ≡ n
∣-untrunc {zero} p = zero , equivFun ∣≃∣' p
∣-untrunc {suc m} = equivFun ∣≃∣'


-- basic properties of ∣

∣-refl : m ≡ n → m ∣ n
∣-refl p = ∣ 1 , +-zero _ ∙ p ∣

∣-trans : l ∣ m → m ∣ n → l ∣ n
∣-trans = PropTrunc.map2 λ {
  (c₁ , p) (c₂ , q) → (c₂ * c₁ , sym (*-assoc c₂ c₁ _) ∙ cong (c₂ *_) p ∙ q) }

∣-cancelʳ : ∀ k → (m * suc k) ∣ (n * suc k) → m ∣ n
∣-cancelʳ k = PropTrunc.map λ {
  (c , p) → (c , inj-*sm (sym (*-assoc c _ (suc k)) ∙ p)) }

∣-multʳ : ∀ k → m ∣ n → (m * k) ∣ (n * k)
∣-multʳ k = PropTrunc.map λ {
  (c , p) → (c , *-assoc c _ k ∙ cong (_* k) p) }

∣-zeroˡ : zero ∣ m → zero ≡ m
∣-zeroˡ = equivFun ∣≃∣'

∣-zeroʳ : ∀ m → m ∣ zero
∣-zeroʳ m = ∣ zero , refl ∣

∣-oneˡ : ∀ m → 1 ∣ m
∣-oneˡ m = ∣ m , *-identityʳ m ∣

-- if n > 0, then the constant c (s.t. c * m ≡ n) is also > 0
∣s-untrunc : m ∣ suc n → Σ[ c ∈ ℕ ] (suc c) * m ≡ suc n
∣s-untrunc ∣p∣ with ∣-untrunc ∣p∣
... | (zero  , p) = ⊥.rec (znots p)
... | (suc c , p) = (c , p)

m∣sn→m≤sn : m ∣ suc n → m ≤ suc n
m∣sn→m≤sn {m} {n} = f ∘ ∣s-untrunc
  where f : Σ[ c ∈ ℕ ] (suc c) * m ≡ suc n → Σ[ c ∈ ℕ ] c + m ≡ suc n
        f (c , p) = (c * m) , (+-comm (c * m) m ∙ p)

m∣sn→z<m : m ∣ suc n → zero < m
m∣sn→z<m {zero} p = ⊥.rec (znots (∣-zeroˡ p))
m∣sn→z<m {suc m} p = suc-≤-suc zero-≤

antisym∣ : ∀ {m n} → m ∣ n → n ∣ m → m ≡ n
antisym∣ {zero} {n} z∣n _ = ∣-zeroˡ z∣n
antisym∣ {m} {zero} _ z∣m = sym (∣-zeroˡ z∣m)
antisym∣ {suc m} {suc n} p q = ≤-antisym (m∣sn→m≤sn p) (m∣sn→m≤sn q)

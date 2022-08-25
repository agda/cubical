{-

The Two-Level Type Theory in Cubical Agda

This file contains:

- Lifting internal types to external ones;

- The definitions and some basic facts of external 𝟙, Σ, ℕ and Id types;

- A macro transforming external natural numbers to internal ones.

-}
{-# OPTIONS --safe #-}
module Cubical.Foundations.2LTT where

open import Cubical.Data.Nat.Base
open import Cubical.Foundations.Prelude
open import Agda.Primitive public renaming (SSet to Typeᵉ)

open import Agda.Builtin.List
open import Agda.Builtin.Reflection hiding (Type)
open import Cubical.Reflection.Base

private
  variable
    ℓ ℓ' : Level


{- External Identity Type -}

data _≡ᵉ_ {A : Typeᵉ ℓ} : A → A → Typeᵉ ℓ where
  reflᵉ : {a : A} → a ≡ᵉ a

infix 4 _≡ᵉ_

Idᵉ = _≡ᵉ_

-- Basic operations

_∙ᵉ_ : {A : Typeᵉ ℓ} {a b c : A} → a ≡ᵉ b → a ≡ᵉ c → a ≡ᵉ c
reflᵉ ∙ᵉ reflᵉ = reflᵉ

symᵉ : {A : Typeᵉ ℓ} {a b : A} → a ≡ᵉ b → b ≡ᵉ a
symᵉ reflᵉ = reflᵉ

congᵉ : {A : Typeᵉ ℓ} {B : Typeᵉ ℓ'} → (f : A → B) → {a b : A} → a ≡ᵉ b → f a ≡ᵉ f b
congᵉ f reflᵉ = reflᵉ

cong' : {A : Typeᵉ ℓ} {B : Type ℓ'} → (f : A → B) → {a b : A} → a ≡ᵉ b → f a ≡ f b
cong' f reflᵉ = refl

substᵉ : {A : Typeᵉ ℓ} (P : A → Typeᵉ ℓ') {a b : A} → a ≡ᵉ b → P a → P b
substᵉ P reflᵉ p = p

transportᵉ : {A B : Typeᵉ ℓ} → A ≡ᵉ B → A → B
transportᵉ reflᵉ a = a

-- external identity type satisfies UIP

Kᵉ : {A : Typeᵉ ℓ} {a b : A} → (p q : a ≡ᵉ b) → p ≡ᵉ q
Kᵉ reflᵉ reflᵉ = reflᵉ


{- External Inhomogeneous Equality -}

data IdPᵉ {A : Typeᵉ ℓ} {B : A → Typeᵉ ℓ'} :
  {a b : A} → a ≡ᵉ b → B a → B b → Typeᵉ (ℓ-max ℓ ℓ')
  where
  reflᵉ : {a : A} {b : B a} → IdPᵉ reflᵉ b b

-- Basic operations

symPᵉ :
  {A : Typeᵉ ℓ} {B : A → Typeᵉ ℓ'}
  {a b : A} (p : a ≡ᵉ b)
  {x : B a} {y : B b}
  → IdPᵉ p x y → IdPᵉ (symᵉ p) y x
symPᵉ reflᵉ reflᵉ = reflᵉ

congPᵉ :
  {A : Typeᵉ ℓ} {B : A → Typeᵉ ℓ'}
  (f : (a : A) → B a)
  {a b : A} (p : a ≡ᵉ b)
  → IdPᵉ p (f a) (f b)
congPᵉ f reflᵉ = reflᵉ

substᵉ-filler :
  {A : Typeᵉ ℓ} {B : A → Typeᵉ ℓ'}
  {a b : A} (p : a ≡ᵉ b) (b : B a)
  → IdPᵉ p b (substᵉ B p b)
substᵉ-filler reflᵉ b = reflᵉ

transport-fillerᵉ :
  {A B : Typeᵉ ℓ}
  (p : A ≡ᵉ B) (a : A)
  → IdPᵉ p a (transportᵉ p a)
transport-fillerᵉ reflᵉ a = reflᵉ


{- Lift Internal Types to the External Universes -}

data Exo (A : Type ℓ) : Typeᵉ ℓ where
  exo : A → Exo A

-- Transform the external inhabitants to internal ones

int : {A : Type ℓ} → Exo A → A
int (exo a) = a

-- Lifted types are exo-equivalent to the original internal ones.

int-exo : {A : Type ℓ} → (a : Exo A) → exo (int a) ≡ᵉ a
int-exo (exo a) = reflᵉ

exo-int : {A : Type ℓ} → (a : A) → int (exo a) ≡ a
exo-int a = refl

-- Transform exteral propositional equality to internal path

coerceᵉ : {A : Type ℓ} {a b : Exo A} → a ≡ᵉ b → int a ≡ int b
coerceᵉ reflᵉ = refl


{- External Natural Number -}

data ℕᵉ : Typeᵉ where
  zero : ℕᵉ
  suc  : ℕᵉ → ℕᵉ

pattern 0ᵉ = zero
pattern 1ᵉ = suc 0ᵉ
pattern 2ᵉ = suc 1ᵉ
pattern 3ᵉ = suc 2ᵉ
pattern 4ᵉ = suc 3ᵉ

-- Transform exteral natural numbers to internal ones

ℕᵉ→ℕ : ℕᵉ → ℕ
ℕᵉ→ℕ zero = 0
ℕᵉ→ℕ (suc n) = suc (ℕᵉ→ℕ n)

-- Transform internal natural numbers to external ones
-- In fact it's impossible in Agda's 2LTT, so we could only use a macro.

ℕ→ℕᵉTerm : ℕ → Term
ℕ→ℕᵉTerm 0 = quoteTerm ℕᵉ.zero
ℕ→ℕᵉTerm (suc n) = con (quote ℕᵉ.suc) (ℕ→ℕᵉTerm n v∷ [])

macro
  ℕ→ℕᵉ : ℕ → Term → TC Unit
  ℕ→ℕᵉ n t = unify t (ℕ→ℕᵉTerm n)

-- An example

test : ℕ→ℕᵉ 3 ≡ᵉ 3ᵉ
test = reflᵉ


{- External Unit Type -}

data Unitᵉ : Typeᵉ where
  tt : Unitᵉ

data Unit*ᵉ {ℓ : Level} : Typeᵉ ℓ where
  tt*ᵉ : Unit*ᵉ


{- External Σ-Type -}

record Σᵉ (A : Typeᵉ ℓ)(B : A → Typeᵉ ℓ') : Typeᵉ (ℓ-max ℓ ℓ') where
  constructor _,_
  field
    fst : A
    snd : B fst

open Σᵉ public

Σᵉ-syntax : ∀ {ℓ ℓ'} (A : Typeᵉ ℓ) (B : A → Typeᵉ ℓ') → Typeᵉ (ℓ-max ℓ ℓ')
Σᵉ-syntax = Σᵉ

syntax Σᵉ-syntax A (λ x → B) = Σᵉ[ x ∈ A ] B

-- External (non-dependent) product

_×ᵉ_ : ∀ {ℓ ℓ'} (A : Typeᵉ ℓ) (B : Typeᵉ ℓ') → Typeᵉ (ℓ-max ℓ ℓ')
A ×ᵉ B = Σᵉ A (λ _ → B)

infixr 5 _×ᵉ_

-- Currying and uncurrying

curryᵉ :
  {A : Typeᵉ ℓ} {B : A → Typeᵉ ℓ'} {C : (a : A) → B a → Typeᵉ ℓ'}
  → (((a , b) : Σᵉ A B) → C a b)
  → (a : A) → (b : B a) → C a b
curryᵉ f a b = f (a , b)

uncurryᵉ :
  {A : Typeᵉ ℓ} {B : A → Typeᵉ ℓ'} {C : (a : A) → B a → Typeᵉ ℓ'}
  → ((a : A) → (b : B a) → C a b)
  → ((a , b) : Σᵉ A B) → C a b
uncurryᵉ f (a , b) = f a b

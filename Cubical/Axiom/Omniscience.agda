{-# OPTIONS --cubical --no-import-sorts #-}

module Cubical.Axiom.Omniscience where

open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport

open import Cubical.Data.Bool
  renaming (Bool to 𝟚; Bool→Type to ⟨_⟩)
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum as Sum

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Relation.Nullary

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ

-- Lesser limited principle of omniscience
--
-- If two decidable predicates cannot both be satisfied, we can
-- determine that one predicate cannot be satisfied.
LLPO : Type ℓ → Type ℓ
LLPO A
  = ∀(P Q : A → 𝟚)
  → (∀ x y → ⟨ P x ⟩ → ⟨ Q y ⟩ → ⊥)
  → ∥ (∀ x → ¬ ⟨ P x ⟩) ⊎ (∀ y → ¬ ⟨ Q y ⟩) ∥₁

isPropLLPO : isProp (LLPO A)
isPropLLPO = isPropΠ3 λ _ _ _ → squash₁

-- As above, but without ensuring propositionality
LLPO∞ : Type ℓ → Type ℓ
LLPO∞ A
  = ∀(P Q : A → 𝟚)
  → (∀ x y → ⟨ P x ⟩ → ⟨ Q y ⟩ → ⊥)
  → (∀ x → ¬ ⟨ P x ⟩) ⊎ (∀ y → ¬ ⟨ Q y ⟩)

LLPO∞→LLPO : LLPO∞ A → LLPO A
LLPO∞→LLPO llpo' P Q ¬both = ∣ llpo' P Q ¬both ∣₁

-- Weak limited principle of omniscience
--
-- It is decidable whether or not a decidable predicate never holds.
WLPO : Type ℓ → Type ℓ
WLPO A = ∀(P : A → 𝟚) → Dec (∀ x → ¬ ⟨ P x ⟩)

WLPO' : Type ℓ → Type ℓ
WLPO' A = ∀(P : A → 𝟚) → Dec (P ≡ const false)

isPropWLPO : isProp (WLPO A)
isPropWLPO = isPropΠ λ P → isPropDec (isPropΠ λ x → isProp¬ ⟨ P x ⟩)

isPropWLPO' : isProp (WLPO' A)
isPropWLPO' = isPropΠ λ P → isPropDec (isSet→ isSetBool P (const false))

module WLPO≃ where
  points : (P : A → 𝟚) → P ≡ const false → ∀ x → ¬ ⟨ P x ⟩
  points P p x = subst (λ Q → ⟨ Q x ⟩) p

  total : (P : A → 𝟚) → (∀ x → ¬ ⟨ P x ⟩) → P ≡ const false
  total P never i x with P x | never x
  ... | false | _ = false
  ... | true  | ¬⊤ = Empty.rec {A = true ≡ false} (¬⊤ _) i

  open Iso

  total≡points : ∀(P : A → 𝟚) → (P ≡ const false) ≡ (∀ x → ¬ ⟨ P x ⟩)
  total≡points P = isoToPath λ where
    .fun → points P
    .inv → total P
    .rightInv never → isPropΠ (λ x → isProp¬ ⟨ P x ⟩) _ never
    .leftInv α≡f → isSet→ isSetBool P (const false) _ α≡f

WLPO≡WLPO' : WLPO A ≡ WLPO' A
WLPO≡WLPO' {A = A} i = (P : A → 𝟚) → Dec (WLPO≃.total≡points P (~ i))

WLPO→LLPO∞ : WLPO A → LLPO∞ A
WLPO→LLPO∞ {A = A} womn P Q ¬both with womn P
... | yes ∀¬P = inl ∀¬P
... | no ¬∀¬P = inr ∀¬Q where
  ∀¬Q : ∀ y → ¬ ⟨ Q y ⟩
  ∀¬Q y Qy = ¬∀¬P (λ x Px → ¬both x y Px Qy)

-- Limited principle of omniscience
--
-- Either a decidable predicate never holds, or it does
LPO : Type ℓ → Type ℓ
LPO A = ∀(P : A → 𝟚) → (∀ x → ¬ ⟨ P x ⟩) ⊎ ∥ Σ[ x ∈ A ] ⟨ P x ⟩ ∥₁

LPO→WLPO : LPO A → WLPO A
LPO→WLPO omn P with omn P
... | inl ∀¬P = yes ∀¬P
... | inr ∃P  = no λ ∀¬P → PT.rec isProp⊥ (uncurry ∀¬P) ∃P

-- As above, but without truncation.
LPO∞ : Type ℓ → Type ℓ
LPO∞ A = ∀(P : A → 𝟚) → (∀ x → ¬ ⟨ P x ⟩) ⊎ (Σ[ x ∈ A ] ⟨ P x ⟩)

LPO∞→LPO : LPO∞ A → LPO A
LPO∞→LPO omn P = Sum.map (idfun _) ∣_∣₁ (omn P)

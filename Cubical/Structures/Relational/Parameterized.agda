{-

A parameterized family of structures S can be combined into a single structure:
X ↦ (a : A) → S a X

-}
{-# OPTIONS --safe #-}
module Cubical.Structures.Relational.Parameterized where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.RelationalStructure
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation
open import Cubical.HITs.SetQuotients

open import Cubical.Structures.Parameterized

private
  variable
    ℓ ℓ₀ ℓ₁ ℓ₁' ℓ₁'' : Level

-- Structured relations

module _ (A : Type ℓ₀) where

  ParamRelStr : {S : A → Type ℓ → Type ℓ₁}
    → (∀ a → StrRel (S a) ℓ₁')
    → StrRel (ParamStructure A S) (ℓ-max ℓ₀ ℓ₁')
  ParamRelStr ρ R s t =
    (a : A) → ρ a R (s a) (t a)

  paramSuitableRel : {S : A → Type ℓ → Type ℓ₁} {ρ : ∀ a → StrRel (S a) ℓ₁'}
    → (∀ a → SuitableStrRel (S a) (ρ a))
    → SuitableStrRel (ParamStructure A S) (ParamRelStr ρ)
  paramSuitableRel {ρ = ρ} θ .quo (X , f) R r .fst .fst a =
    θ a .quo (X , f a) R (r a) .fst .fst
  paramSuitableRel {ρ = ρ} θ .quo (X , f) R r .fst .snd a =
    θ a .quo (X , f a) R (r a) .fst .snd
  paramSuitableRel {ρ = ρ} θ .quo (X , f) R r .snd (q , c) i .fst a =
    θ a .quo (X , f a) R (r a) .snd (q a , c a) i .fst
  paramSuitableRel {ρ = ρ} θ .quo (X , f) R r .snd (q , c) i .snd a =
    θ a .quo (X , f a) R (r a) .snd (q a , c a) i .snd
  paramSuitableRel {ρ = ρ} θ .symmetric R r a =
    θ a .symmetric R (r a)
  paramSuitableRel {ρ = ρ} θ .transitive R R' r r' a =
    θ a .transitive R R' (r a) (r' a)
  paramSuitableRel {ρ = ρ} θ .set setX =
    isSetΠ λ a → θ a .set setX
  paramSuitableRel {ρ = ρ} θ .prop propR s t =
    isPropΠ λ a → θ a .prop propR (s a) (t a)

  paramRelMatchesEquiv : {S : A → Type ℓ → Type ℓ₁}
    (ρ : ∀ a → StrRel (S a) ℓ₁') {ι : ∀ a → StrEquiv (S a) ℓ₁''}
    → (∀ a → StrRelMatchesEquiv (ρ a) (ι a))
    → StrRelMatchesEquiv (ParamRelStr ρ) (ParamEquivStr A ι)
  paramRelMatchesEquiv ρ μ _ _ e = equivΠCod λ a → μ a _ _ e

  paramRelAction : {S : A → Type ℓ → Type ℓ₁} {ρ : ∀ a → StrRel (S a) ℓ₁'}
    → (∀ a → StrRelAction (ρ a))
    → StrRelAction (ParamRelStr ρ)
  paramRelAction α .actStr f s a = α a .actStr f (s a)
  paramRelAction α .actStrId s = funExt λ a → α a .actStrId (s a)
  paramRelAction α .actRel h _ _ r a = α a .actRel h _ _ (r a)

  -- Detransitivity of ParamRelStr would depend on choice in general, so
  -- we don't get positivity

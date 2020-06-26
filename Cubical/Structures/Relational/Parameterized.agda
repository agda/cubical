{-

A parameterized family of structures S can be combined into a single structure:
X ↦ (a : A) → S a X

-}
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Structures.Relational.Parameterized where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.RelationalStructure
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Sigma
open import Cubical.HITs.SetQuotients

open import Cubical.Structures.Parameterized

private
  variable
    ℓ ℓ₀ ℓ₁ ℓ₁' : Level

-- Structured relations

module _ (A : Type ℓ₀) where

  preservesSetsParam : {S : A → Type ℓ → Type ℓ₁}
    → (∀ a → preservesSets (S a)) → preservesSets (ParamStructure A S)
  preservesSetsParam p setX = isSetΠ λ a → p a setX

  ParamRelStr : {S : A → Type ℓ → Type ℓ₁} {ℓ₁' : Level}
    → (∀ a → StrRel (S a) ℓ₁')
    → StrRel (ParamStructure A S) (ℓ-max ℓ₀ ℓ₁')
  ParamRelStr ρ R s t =
    (a : A) → ρ a R (s a) (t a)

  open SuitableStrRel

  paramSuitableRel : {S : A → Type ℓ → Type ℓ₁} {ℓ₁' : Level}
    {ρ : ∀ a → StrRel (S a) ℓ₁'}
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
  paramSuitableRel {ρ = ρ} θ .prop propR s t =
    isPropΠ λ a → θ a .prop propR (s a) (t a)

  paramRelMatchesEquiv : {S : A → Type ℓ → Type ℓ₁} {ℓ₁' : Level}
    (ρ : ∀ a → StrRel (S a) ℓ₁') {ι : ∀ a → StrEquiv (S a) ℓ₁'}
    → (∀ a → StrRelMatchesEquiv (ρ a) (ι a))
    → StrRelMatchesEquiv (ParamRelStr ρ) (ParamEquivStr A ι)
  paramRelMatchesEquiv ρ μ _ _ e = equivΠCod λ a → μ a _ _ e

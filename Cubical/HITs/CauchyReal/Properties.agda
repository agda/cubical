{-# OPTIONS --safe #-}
module Cubical.HITs.CauchyReal.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Rationals.Base
open import Cubical.Data.Rationals.Order
open import Cubical.Data.Rationals.Properties
open import Cubical.Data.PositiveRational.Base
open import Cubical.HITs.CauchyReal.Base

module _
  {a b}
  (A : ℝ → Type a)
  (B : ∀ {ε x y} → A x → A y → x ~[ ε ] y → Type b)
  where

  record DepCℝ (x : Cℝ) : Type (ℓ-max a b) where
    inductive
    field
      approx : ∀ (ε : ℚ₊) → A (x .approx ε)
      isCauchy : ∀ (δ ε : ℚ₊) → B (approx δ) (approx ε) (x .isCauchy δ ε)

  open DepCℝ public

module _
  {a b}
  (A : ℝ → Type a)
  (B : ∀ {ε x y} → A x → A y → x ~[ ε ] y → Type b)
  (case-rat : ∀ (q : ℚ) →
              A (rat q))
  (case-lim : ∀ (x : Cℝ) →
              ∀ (x′ : DepCℝ A B x) →
              A (lim x))
  (case-eqℝ : ∀ (u v : ℝ) (h : ∀ ε → u ~[ ε ] v) →
              ∀ (u′ : A u) (v′ : A v) (h′ : ∀ ε → B u′ v′ (h ε)) →
              PathP (λ i → A (eqℝ u v h i)) u′ v′)
  (case-rat~rat : ∀ q r ε (h₁ : - (ε .value) < q - r) (h₂ : q - r < ε .value) →
                  B (case-rat q) (case-rat r) (rat~rat q r ε h₁ h₂))
  (case-rat~lim : ∀ q y ε η (ξ : rat q ~[ ε ] y .approx η) →
                  ∀ (y′ : DepCℝ A B y) (ξ′ : B (case-rat q) (y′ .approx η) ξ) →
                  B (case-rat q) (case-lim y y′) (rat~lim q y ε η ξ))
  (case-lim~rat : ∀ x r ε δ (ξ : x .approx δ ~[ ε ] rat r) →
                  ∀ (x′ : DepCℝ A B x) (ξ′ : B (x′ .approx δ) (case-rat r) ξ) →
                  B (case-lim x x′) (case-rat r) (lim~rat x r ε δ ξ))
  (case-lim~lim : ∀ x y ε δ η (ξ : x .approx δ ~[ ε ] y .approx η) →
                  ∀ (x′ : DepCℝ A B x) (y′ : DepCℝ A B y) (ξ′ : B (x′ .approx δ) (y′ .approx η) ξ) →
                  B (case-lim x x′) (case-lim y y′) (lim~lim x y ε δ η ξ))
  (case-squash~ : ∀ u v ε (ξ ζ : u ~[ ε ] v)
                  (u′ : A u) (v′ : A v) (ξ′ : B u′ v′ ξ) (ζ′ : B u′ v′ ζ) →
                  PathP (λ i → B u′ v′ (squash~ u v ε ξ ζ i)) ξ′ ζ′)
  where

  elim-ℝ : ∀ (u : ℝ) → A u
  elim-Cℝ : ∀ (x : Cℝ) → DepCℝ A B x
  elim-rel : ∀ {ε x y} (ξ : x ~[ ε ] y) → B (elim-ℝ x) (elim-ℝ y) ξ
  elim-ℝ (rat q)       = case-rat q
  elim-ℝ (lim x)       = case-lim x (elim-Cℝ x)
  elim-ℝ (eqℝ u v h i) = case-eqℝ u v h (elim-ℝ u) (elim-ℝ v) (λ ε → elim-rel (h ε)) i
  elim-Cℝ x = record { approx = λ ε → elim-ℝ (x .approx ε)
                     ; isCauchy = λ δ ε → elim-rel (x .isCauchy δ ε)
                     }
  elim-rel (rat~rat q r ε h₁ h₂) = case-rat~rat q r ε h₁ h₂
  elim-rel (rat~lim q y ε η ξ)   = case-rat~lim q y ε η ξ (elim-Cℝ y) (elim-rel ξ)
  elim-rel (lim~rat x r ε δ ξ)   = case-lim~rat x r ε δ ξ (elim-Cℝ x) (elim-rel ξ)
  elim-rel (lim~lim x y ε δ η ξ) = case-lim~lim x y ε δ η ξ (elim-Cℝ x) (elim-Cℝ y) (elim-rel ξ)
  elim-rel (squash~ u v ε ξ ζ i) = case-squash~ u v ε ξ ζ (elim-ℝ u) (elim-ℝ v) (elim-rel ξ) (elim-rel ζ) i

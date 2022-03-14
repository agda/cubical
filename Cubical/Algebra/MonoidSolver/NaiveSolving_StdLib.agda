module Cubical.Algebra.MonoidSolver.NaiveSolving_StdLib where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Functions.Logic

open import Agda.Builtin.Reflection
  hiding (Type) renaming (normalise to normalizeTerm)
--open import Agda.Builtin.String

open import Cubical.Reflection.Base

open import Cubical.Data.Maybe
open import Cubical.Data.Sigma
open import Cubical.Data.FinData using (Fin)
open import Cubical.Data.Nat using (ℕ)
--open import Cubical.Data.Nat.Order using (zero-≤)
open import Cubical.Data.List
open import Cubical.Data.Bool
open import Cubical.Data.Vec using (Vec; lookup)

open import Cubical.Algebra.Monoid

private
  variable
    ℓ : Level

infixl 7 _⊗_

-- Expression in a type M with n variables
data Expr {ℓ} (M : Type ℓ) : Type ℓ where
  ε⊗  : Expr M
  V   : M → Expr M
  _⊗_ : Expr M → Expr M → Expr M

module Eval (M : Monoid ℓ) where
  open MonoidStr (snd M)

  -- evaluation of an expression (without normalization)
  ⟦_⟧ : Expr ⟨ M ⟩ → ⟨ M ⟩
  ⟦ ε⊗ ⟧ = ε
  ⟦ V m ⟧ = m
  ⟦ e₁ ⊗ e₂ ⟧ = ⟦ e₁ ⟧ · ⟦ e₂ ⟧

  -- evaluation & normalization of an expression
  ⟦_N⟧ : Expr ⟨ M ⟩ → ⟨ M ⟩ → ⟨ M ⟩
  ⟦ ε⊗ N⟧ m    = m
  ⟦ V n N⟧ m   = n · m
  ⟦ e₁ ⊗ e₂ N⟧ m = ⟦ e₁ N⟧ (⟦ e₂ N⟧ m)

  ⟦_N⟧ε :  Expr ⟨ M ⟩ → ⟨ M ⟩
  ⟦ e N⟧ε = ⟦ e N⟧ ε

module _ (M : Monoid ℓ) where
  open Eval M
  open MonoidStr (snd M)

  -- proof that evaluation of an expression is invariant under normalization
  lemma : ∀ e m → ⟦ e N⟧ m ≡ ⟦ e ⟧ · m
  lemma ε⊗ _ = sym (lid _ )
  lemma (V n) _ = refl
  lemma (e₁ ⊗ e₂) m =
    ⟦ e₁ N⟧ (⟦ e₂ N⟧ m)   ≡⟨ cong (λ n → ⟦ e₁ N⟧ n) (lemma e₂ m) ⟩
    ⟦ e₁ N⟧ (⟦ e₂ ⟧ · m)  ≡⟨ lemma e₁ _ ∙ assoc _ _ _ ⟩
    (⟦ e₁ ⟧ · ⟦ e₂ ⟧) · m ∎

  isEqualToNormalform : ∀ e → ⟦ e N⟧ε ≡ ⟦ e ⟧
  isEqualToNormalform e = lemma e ε ∙ rid _


  naiveSolve : (e₁ e₂ : Expr ⟨ M ⟩)
             → (p : ⟦ e₁ ⟧ ≡ ⟦ e₂ ⟧)
             → ⟦ e₁ N⟧ε ≡ ⟦ e₂ N⟧ε
  naiveSolve e₁ e₂ p =
    ⟦ e₁ N⟧ε ≡⟨ isEqualToNormalform e₁ ⟩
    ⟦ e₁ ⟧   ≡⟨ p ⟩
    ⟦ e₂ ⟧   ≡⟨ sym (isEqualToNormalform e₂) ⟩
    ⟦ e₂ N⟧ε ∎

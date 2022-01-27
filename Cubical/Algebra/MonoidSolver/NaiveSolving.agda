module Cubical.Algebra.MonoidSolver.NaiveSolving where

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
data Expr {ℓ} (M : Type ℓ) (n : ℕ) : Type ℓ where
  ε⊗  : Expr M n
  V   : Fin n → Expr M n
  _⊗_ : Expr M n → Expr M n → Expr M n

module Eval (M : Monoid ℓ) where
  open MonoidStr (snd M)

  Env : ℕ → Type ℓ
  Env n = Vec ⟨ M ⟩ n

  -- evaluation of an expression (without normalization)
  ⟦_⟧ : ∀ {n} → Expr ⟨ M ⟩ n → Env n → ⟨ M ⟩
  ⟦ ε⊗ ⟧ v = ε
  ⟦ V i ⟧ v = lookup i v
  ⟦ e₁ ⊗ e₂ ⟧ v = ⟦ e₁ ⟧ v · ⟦ e₂ ⟧ v

  NormalForm : ℕ → Type _
  NormalForm n = List (Fin n)

  -- normalization of an expression
  normalize : ∀ {n} → Expr ⟨ M ⟩ n → NormalForm n
  normalize (V i) = i ∷ []
  normalize ε⊗ = []
  normalize (e₁ ⊗ e₂) = (normalize e₁) ++ (normalize e₂)

  -- evaluation of normalization
  ⟦_⇓⟧ : ∀ {n} → NormalForm n → Env n → ⟨ M ⟩
  ⟦ [] ⇓⟧ v = ε
  ⟦ x ∷ xs ⇓⟧ v = (lookup x v) · ⟦ xs ⇓⟧ v

module _ (M : Monoid ℓ) where
  open Eval M
  open MonoidStr (snd M)

  -- proof that evaluation of an expression is invariant under normalization
  isEqualToNormalform : (n : ℕ)
                      → (e : Expr ⟨ M ⟩ n)
                      → (v : Env n)
                      → ⟦ (normalize e) ⇓⟧ v ≡ ⟦ e ⟧ v
  isEqualToNormalform n (V i) v = rid _
  isEqualToNormalform n ε⊗ v = refl
  isEqualToNormalform n (e₁ ⊗ e₂) v =
    ⟦ (normalize e₁) ++ (normalize e₂) ⇓⟧ v
      ≡⟨ lemma (normalize e₁) (normalize e₂) ⟩
    ⟦ (normalize e₁) ⇓⟧ v · ⟦ (normalize e₂) ⇓⟧ v
      ≡⟨ cong₂ _·_ (isEqualToNormalform n e₁ v) (isEqualToNormalform n e₂ v) ⟩
    ⟦ e₁ ⟧ v · ⟦ e₂ ⟧ v
      ∎
    where
      lemma : (l₁ l₂ : NormalForm n)
            → ⟦ l₁ ++ l₂ ⇓⟧ v ≡  ⟦ l₁ ⇓⟧ v · ⟦ l₂ ⇓⟧ v
      lemma [] l₂ = sym (lid _)
      lemma (x ∷ xs) l₂ =
        cong (λ m → (lookup x v) · m) (lemma xs l₂) ∙ assoc _ _ _

  naiveSolve : {n : ℕ}
             → (e₁ e₂ : Expr ⟨ M ⟩ n)
             → (v : Env n)
             → (p : ⟦ (normalize e₁) ⇓⟧ v ≡ ⟦ (normalize e₂) ⇓⟧ v)
             → ⟦ e₁ ⟧ v ≡ ⟦ e₂ ⟧ v
  naiveSolve e₁ e₂ v p =
    ⟦ e₁ ⟧ v              ≡⟨ sym (isEqualToNormalform _ e₁ v) ⟩
    ⟦ (normalize e₁) ⇓⟧ v ≡⟨ p ⟩
    ⟦ (normalize e₂) ⇓⟧ v ≡⟨ isEqualToNormalform _ e₂ v ⟩
    ⟦ e₂ ⟧ v              ∎

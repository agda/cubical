{-# OPTIONS --safe #-}
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
data Expr (M : Type ℓ) (n : ℕ) : Type ℓ where
  ∣   : Fin n → Expr M n
  ε⊗  : Expr M n
  _⊗_ : Expr M n → Expr M n → Expr M n


module Eval (M : Monoid ℓ) where
  open MonoidStr (snd M)

  Env : ℕ → Type ℓ
  Env n = Vec ⟨ M ⟩ n

  -- evaluation of an expression (without normalization)
  ⟦_⟧ : ∀{n} → Expr ⟨ M ⟩ n → Env n → ⟨ M ⟩
  ⟦ ε⊗ ⟧ v = ε
  ⟦ ∣ i ⟧ v = lookup i v
  ⟦ e₁ ⊗ e₂ ⟧ v = ⟦ e₁ ⟧ v · ⟦ e₂ ⟧ v

  NormalForm : ℕ → Type _
  NormalForm n = List (Fin n)

  -- normalization of an expression
  normalize : ∀{n} → Expr ⟨ M ⟩ n → NormalForm n
  normalize (∣ i) = i ∷ []
  normalize ε⊗ = []
  normalize (e₁ ⊗ e₂) = (normalize e₁) ++ (normalize e₂)

  -- evaluation of normalization
  eval : ∀ {n} → NormalForm n → Env n → ⟨ M ⟩
  eval [] v = ε
  eval (x ∷ xs) v = (lookup x v) · (eval xs v)

module EqualityToNormalform (M : Monoid ℓ) where
  open Eval M
  open MonoidStr (snd M)

  -- proof that evaluation of an expression is invariant under normalization
  isEqualToNormalform : (n : ℕ)
                      → (e : Expr ⟨ M ⟩ n)
                      → (v : Env n)
                      → eval (normalize e) v ≡ ⟦ e ⟧ v
  isEqualToNormalform n (∣ i) v = rid _
  isEqualToNormalform n ε⊗ v = refl
  isEqualToNormalform n (e₁ ⊗ e₂) v =
    eval ((normalize e₁) ++ (normalize e₂)) v
      ≡⟨ lemma (normalize e₁) (normalize e₂) ⟩
    (eval (normalize e₁) v) · (eval (normalize e₂) v)
      ≡⟨ cong₂ _·_ (isEqualToNormalform n e₁ v) (isEqualToNormalform n e₂ v) ⟩
    ⟦ e₁ ⟧ v · ⟦ e₂ ⟧ v
      ∎
    where
      lemma : (l₁ l₂ : NormalForm n)
            → eval (l₁ ++ l₂) v ≡  eval l₁ v · eval l₂ v
      lemma [] l₂ = sym (lid _)
      lemma (x ∷ xs) l₂ =
        cong (λ m → (lookup x v) · m) (lemma xs l₂) ∙ assoc _ _ _

  solve : {n : ℕ}
        → (e₁ e₂ : Expr ⟨ M ⟩ n)
        → (v : Env n)
        → (p : eval (normalize e₁) v ≡ eval (normalize e₂) v)
        → ⟦ e₁ ⟧ v ≡ ⟦ e₂ ⟧ v
  solve e₁ e₂ v p =
    ⟦ e₁ ⟧ v              ≡⟨ sym (isEqualToNormalform _ e₁ v) ⟩
    eval (normalize e₁) v ≡⟨ p ⟩
    eval (normalize e₂) v ≡⟨ isEqualToNormalform _ e₂ v ⟩
    ⟦ e₂ ⟧ v              ∎

solve : (M : Monoid ℓ)
        {n : ℕ} (e₁ e₂ : Expr ⟨ M ⟩ n) (v : Eval.Env M n)
        (p :  Eval.eval M (Eval.normalize M e₁) v ≡ Eval.eval M (Eval.normalize M e₂) v)
        → _
solve M = EqualityToNormalform.solve M

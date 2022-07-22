{-# OPTIONS --safe #-}
module Cubical.Tactics.MonoidSolver.Solver where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Data.FinData using (Fin)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.List
open import Cubical.Data.Vec using (Vec; lookup)

open import Cubical.Algebra.Monoid

open import Cubical.Tactics.MonoidSolver.MonoidExpression


private
  variable
    ℓ : Level


module Eval (M : Monoid ℓ) where
  open MonoidStr (snd M)

  Env : ℕ → Type ℓ
  Env n = Vec ⟨ M ⟩ n

  -- evaluation of an expression (without normalization)
  ⟦_⟧ : ∀{n} → Expr ⟨ M ⟩ n → Env n → ⟨ M ⟩
  ⟦ ε⊗ ⟧ v      = ε
  ⟦ ∣ i ⟧ v     = lookup i v
  ⟦ e₁ ⊗ e₂ ⟧ v = ⟦ e₁ ⟧ v · ⟦ e₂ ⟧ v

  NormalForm : ℕ → Type _
  NormalForm n = List (Fin n)

  -- normalization of an expression
  normalize : ∀{n} → Expr ⟨ M ⟩ n → NormalForm n
  normalize (∣ i)     = i ∷ []
  normalize ε⊗        = []
  normalize (e₁ ⊗ e₂) = (normalize e₁) ++ (normalize e₂)

  -- evaluation of normalform
  eval : ∀ {n} → NormalForm n → Env n → ⟨ M ⟩
  eval [] v       = ε
  eval (x ∷ xs) v = (lookup x v) · (eval xs v)

  -- some calculation
  evalIsHom : ∀ {n} (x y : NormalForm n) (v : Env n)
            → eval (x ++ y) v ≡ eval x v · eval y v
  evalIsHom [] y v       = sym (·IdL _)
  evalIsHom (x ∷ xs) y v =
    cong (λ m → (lookup x v) · m) (evalIsHom xs y v) ∙ ·Assoc _ _ _

module EqualityToNormalform (M : Monoid ℓ) where
  open Eval M
  open MonoidStr (snd M)

  -- proof that evaluation of an expression is invariant under normalization
  isEqualToNormalform : (n : ℕ)
                      → (e : Expr ⟨ M ⟩ n)
                      → (v : Env n)
                      → eval (normalize e) v ≡ ⟦ e ⟧ v
  isEqualToNormalform n (∣ i) v     = ·IdR _
  isEqualToNormalform n ε⊗ v        = refl
  isEqualToNormalform n (e₁ ⊗ e₂) v =
    eval ((normalize e₁) ++ (normalize e₂)) v         ≡⟨ evalIsHom (normalize e₁) (normalize e₂) v ⟩
    (eval (normalize e₁) v) · (eval (normalize e₂) v) ≡⟨ cong₂ _·_ (isEqualToNormalform n e₁ v) (isEqualToNormalform n e₂ v) ⟩
    ⟦ e₁ ⟧ v · ⟦ e₂ ⟧ v                               ∎

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

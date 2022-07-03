{-# OPTIONS --safe #-}
module Cubical.Tactics.MonoidSolver.CommSolver where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Data.FinData
open import Cubical.Data.Nat using (ℕ; _+_; iter)
open import Cubical.Data.Vec

open import Cubical.Algebra.CommMonoid

open import Cubical.Tactics.MonoidSolver.MonoidExpression

private
  variable
    ℓ : Level


module Eval (M : CommMonoid ℓ) where
  open CommMonoidStr (snd M)
  open CommMonoidTheory M

  Env : ℕ → Type ℓ
  Env n = Vec ⟨ M ⟩ n

  -- evaluation of an expression (without normalization)
  ⟦_⟧ : ∀{n} → Expr ⟨ M ⟩ n → Env n → ⟨ M ⟩
  ⟦ ε⊗ ⟧ v      = ε
  ⟦ ∣ i ⟧ v     = lookup i v
  ⟦ e₁ ⊗ e₂ ⟧ v = ⟦ e₁ ⟧ v · ⟦ e₂ ⟧ v

  -- a normalform is a vector of multiplicities, counting the occurances of each variable in an expression
  NormalForm : ℕ → Type _
  NormalForm n = Vec ℕ n

  _⊞_ : {n : ℕ} → NormalForm n → NormalForm n → NormalForm n
  x ⊞ y = zipWith _+_ x y

  emptyForm : {n : ℕ} → NormalForm n
  emptyForm = replicate 0

  -- e[ i ] is the i-th unit vector
  e[_] : {n : ℕ} → Fin n → NormalForm n
  e[ Fin.zero ]    = 1 ∷ emptyForm
  e[ (Fin.suc j) ] = 0 ∷ e[ j ]

  -- normalization of an expression
  normalize : {n : ℕ} → Expr ⟨ M ⟩ n → NormalForm n
  normalize (∣ i)     = e[ i ]
  normalize ε⊗        = emptyForm
  normalize (e₁ ⊗ e₂) = (normalize e₁) ⊞ (normalize e₂)

  -- evaluation of normalform
  eval : {n : ℕ} → NormalForm n → Env n → ⟨ M ⟩
  eval [] v = ε
  eval (x ∷ xs) (v ∷ vs) = iter x (λ w → v · w) (eval xs vs)


  -- some calculations
  emptyFormEvaluatesToε : {n : ℕ} (v : Env n) → eval emptyForm v ≡ ε
  emptyFormEvaluatesToε [] = refl
  emptyFormEvaluatesToε (v ∷ vs) = emptyFormEvaluatesToε vs

  UnitVecEvaluatesToVar : ∀{n} (i : Fin n) (v : Env n) →  eval e[ i ] v ≡ lookup i v
  UnitVecEvaluatesToVar zero (v ∷ vs) =
    v · eval emptyForm vs ≡⟨ cong₂ _·_ refl (emptyFormEvaluatesToε vs) ⟩
    v · ε                 ≡⟨ ·IdR _ ⟩
    v                     ∎
  UnitVecEvaluatesToVar (suc i) (v ∷ vs) = UnitVecEvaluatesToVar i vs

  evalIsHom : ∀ {n} (x y : NormalForm n) (v : Env n)
            → eval (x ⊞ y) v ≡ (eval x v) · (eval y v)
  evalIsHom [] [] v = sym (·IdL _)
  evalIsHom (x ∷ xs) (y ∷ ys) (v ∷ vs) =
    lemma x y (evalIsHom xs ys vs)
      where
      lemma : ∀ x y {a b c}(p : a ≡ b · c)
            → iter (x + y) (v ·_) a ≡ iter x (v ·_) b · iter y (v ·_) c
      lemma 0 0 p = p
      lemma 0 (ℕ.suc y) p = (cong₂ _·_ refl (lemma 0 y p)) ∙ commAssocl _ _ _
      lemma (ℕ.suc x) y p = (cong₂ _·_ refl (lemma x y p)) ∙ ·Assoc _ _ _

module EqualityToNormalform (M : CommMonoid ℓ) where
  open Eval M
  open CommMonoidStr (snd M)

  -- proof that evaluation of an expression is invariant under normalization
  isEqualToNormalform : {n : ℕ}
                      → (e : Expr ⟨ M ⟩ n)
                      → (v : Env n)
                      → eval (normalize e) v ≡ ⟦ e ⟧ v
  isEqualToNormalform ε⊗ v = emptyFormEvaluatesToε v
  isEqualToNormalform (∣ i) v = UnitVecEvaluatesToVar i v
  isEqualToNormalform (e₁ ⊗ e₂) v =
    eval ((normalize e₁) ⊞ (normalize e₂)) v          ≡⟨ evalIsHom (normalize e₁) (normalize e₂) v ⟩
    (eval (normalize e₁) v) · (eval (normalize e₂) v) ≡⟨ cong₂ _·_ (isEqualToNormalform e₁ v) (isEqualToNormalform e₂ v) ⟩
    ⟦ e₁ ⟧ v · ⟦ e₂ ⟧ v                               ∎

  solve : {n : ℕ}
        → (e₁ e₂ : Expr ⟨ M ⟩ n)
        → (v : Env n)
        → (p : eval (normalize e₁) v ≡ eval (normalize e₂) v)
        → ⟦ e₁ ⟧ v ≡ ⟦ e₂ ⟧ v
  solve e₁ e₂ v p =
    ⟦ e₁ ⟧ v              ≡⟨ sym (isEqualToNormalform e₁ v) ⟩
    eval (normalize e₁) v ≡⟨ p ⟩
    eval (normalize e₂) v ≡⟨ isEqualToNormalform e₂ v ⟩
    ⟦ e₂ ⟧ v              ∎

solve : (M : CommMonoid ℓ)
        {n : ℕ} (e₁ e₂ : Expr ⟨ M ⟩ n) (v : Eval.Env M n)
        (p :  Eval.eval M (Eval.normalize M e₁) v ≡ Eval.eval M (Eval.normalize M e₂) v)
        → _
solve M = EqualityToNormalform.solve M

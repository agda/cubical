module Cubical.Tactics.CommRingSolverFast.AlgebraExpression where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.FinData
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Nat.Order using (zero-≤)
open import Cubical.Data.Vec.Base
open import Cubical.Tactics.CommRingSolverFast.RawRing
open import Cubical.Tactics.CommRingSolverFast.RawAlgebra renaming (⟨_⟩ to ⟨_⟩ₐ)

open import Agda.Builtin.Reflection hiding (Type)
open import Agda.Builtin.String
open import Agda.Builtin.Nat using () renaming (_==_ to _=ℕ_)
open import Cubical.Reflection.Sugar

open import Cubical.Reflection.Base
open import Cubical.Tactics.Reflection.Error
open import Cubical.Tactics.Reflection.Variables

private
  variable
    ℓ ℓ' : Level

infixl 6 _+'_
infixl 7 -'_
infixl 8 _·'_

-- Expression in an R-Algebra A with n variables
data Expr {ℓ} (R : RawRing ℓ) (A : Type ℓ') (n : ℕ) : Type ℓ where
  K : ⟨ R ⟩ → Expr R A n
  ∣ : Fin n → Expr R A n
  _+'_ : Expr R A n → Expr R A n → Expr R A n
  _·'_ : Expr R A n → Expr R A n → Expr R A n
  -'_ : Expr R A n → Expr R A n

module PrettyExpr {ℓ} (R : RawRing ℓ) (A : Type ℓ') (showScalar : ⟨ R ⟩ → TC String) where

 prettyExpr : ∀ {n} → Expr R A n → TC String
 prettyExpr (K x) = showScalar x
 prettyExpr (∣ x) = pure (mkNiceVar (toℕ x))
 prettyExpr (x +' x₁) = do
  x' ← prettyExpr x
  x₁' ← prettyExpr x₁
  pure (x' <> " + " <> x₁')
 prettyExpr (x ·' x₁) = do
  x' ← prettyExpr x
  x₁' ← prettyExpr x₁
  pure ("(" <> x' <> " · " <> x₁' <> ")")
 prettyExpr (-' x) = do
  x' ← prettyExpr x
  pure ("- (" <> x' <> ")")

module Eval (R : RawRing ℓ) (A : RawAlgebra R ℓ') where
  open import Cubical.Data.Vec
  open RawAlgebra A renaming (scalar to scalarₐ)

  ⟦_⟧ : ∀ {n} → Expr R ⟨ A ⟩ₐ n → Vec ⟨ A ⟩ₐ n → ⟨ A ⟩ₐ
  ⟦ K r ⟧ v = scalarₐ r
  ⟦ ∣ k ⟧ v = lookup k v
  ⟦ x +' y ⟧ v = ⟦ x ⟧ v + ⟦ y ⟧ v
  ⟦ x ·' y ⟧ v = ⟦ x ⟧ v · ⟦ y ⟧ v
  ⟦ -' x ⟧ v = - ⟦ x ⟧ v

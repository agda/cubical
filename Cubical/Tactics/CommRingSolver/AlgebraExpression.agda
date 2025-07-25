module Cubical.Tactics.CommRingSolver.AlgebraExpression where

open import Cubical.Foundations.Prelude

open import Cubical.Data.FinData
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Nat.Order using (zero-≤)
open import Cubical.Data.Vec.Base
open import Cubical.Tactics.CommRingSolver.RawRing
open import Cubical.Tactics.CommRingSolver.RawAlgebra renaming (⟨_⟩ to ⟨_⟩ₐ)

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

module Eval (R : RawRing ℓ) (A : RawAlgebra R ℓ') where
  open import Cubical.Data.Vec
  open RawAlgebra A renaming (scalar to scalarₐ)

  ⟦_⟧ : ∀ {n} → Expr R ⟨ A ⟩ₐ n → Vec ⟨ A ⟩ₐ n → ⟨ A ⟩ₐ
  ⟦ K r ⟧ v = scalarₐ r
  ⟦ ∣ k ⟧ v = lookup k v
  ⟦ x +' y ⟧ v = ⟦ x ⟧ v + ⟦ y ⟧ v
  ⟦ x ·' y ⟧ v = ⟦ x ⟧ v · ⟦ y ⟧ v
  ⟦ -' x ⟧ v = - ⟦ x ⟧ v

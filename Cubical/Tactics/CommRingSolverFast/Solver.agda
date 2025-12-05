module Cubical.Tactics.CommRingSolverFast.Solver where

open import Cubical.Foundations.Prelude

open import Cubical.Data.FinData
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma
open import Cubical.Data.Bool
open import Cubical.Data.Nat.Order using (zero-≤)
open import Cubical.Data.Vec.Base
import Cubical.Data.Rationals.Fast as ℚ
open import Cubical.Data.Int.Fast using (pos;negsuc;·AnnihilL)
import Cubical.Data.Int.Fast as ℤ
import Cubical.Data.NatPlusOne as ℕ₊₁
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring
open import Cubical.Tactics.CommRingSolverFast.RawAlgebra renaming (⟨_⟩ to ⟨_⟩ᵣ)
open import Cubical.Tactics.CommRingSolverFast.AlgebraExpression
-- open import Cubical.Tactics.CommRingSolverFast.HornerFormsQ
open import Cubical.Tactics.CommRingSolverFast.EvalHom
open import Cubical.Tactics.CommRingSolverFast.HornerEval
open import Cubical.Tactics.CommRingSolverFast.RawRing
open import Cubical.Algebra.CommRing.Instances.Rationals.Fast
open import Cubical.Tactics.CommRingSolverFast.Utility
open import Cubical.Relation.Nullary.Base using (yes; no)

private
  variable
    ℓ : Level


ℚAsRawRing : RawRing ℓ-zero
ℚAsRawRing = rawring ℚ.ℚ ℚ.[ ℤ.pos 0 / ℕ₊₁.1+ 0 ] ℚ.[ ℤ.pos 0 / ℕ₊₁.1+ 0 ] (ℚ._+_) (ℚ._·_) (λ k → ℚ.- k)

ℚasRawℚAlgebra : RawAlgebra ℚAsRawRing ℓ-zero
ℚasRawℚAlgebra =
 let (R , commringstr 0r 1r _+_ _·_ -_ isCommRing)  = ℚCommRing 
 in rawalgebra ℚ.ℚ (λ z → z) ℚ.[ ℤ.pos 0 / ℕ₊₁.1+ 0 ] ℚ.[ ℤ.pos 0 / ℕ₊₁.1+ 0 ] (ℚ._+_) (ℚ._·_) (λ k → ℚ.- k)



module EqualityToNormalform  where
  R = ℚCommRing

  νR = ℚasRawℚAlgebra

  open Eval ℚAsRawRing νR

  ℚExpr : (n : ℕ) → Type _
  ℚExpr = Expr ℚAsRawRing (fst R)

  eqSpecs :
    {n : ℕ} (e₁ e₂ : ℚExpr n) (xs : Vec (fst R) n) → (⟨ νR ⟩ᵣ × ⟨ νR ⟩ᵣ)
  eqSpecs e₁ e₂ xs =
    ⟦ e₁ ⟧ xs , ⟦ e₂ ⟧ xs


  EqSpecsFnTy : ℕ → Type₀
  EqSpecsFnTy ℕ.zero = (⟨ νR ⟩ᵣ × ⟨ νR ⟩ᵣ)
  EqSpecsFnTy (ℕ.suc x) = ⟨ νR ⟩ᵣ → EqSpecsFnTy x

  toEqSpecsFn : ∀ n → ((xs : Vec (fst R) n) → (⟨ νR ⟩ᵣ × ⟨ νR ⟩ᵣ)) → EqSpecsFnTy n
  toEqSpecsFn ℕ.zero f = f []
  toEqSpecsFn (ℕ.suc n) f v = toEqSpecsFn n λ vs → f (v ∷ vs) 


ℚExpr : (n : ℕ)
        → _
ℚExpr = EqualityToNormalform.ℚExpr 


eqSpecs : 
        (n : ℕ) (e₁ e₂ : ℚExpr n) →
         EqualityToNormalform.EqSpecsFnTy n 
   
eqSpecs n e₁ e₂ =
 EqualityToNormalform.toEqSpecsFn n
   (EqualityToNormalform.eqSpecs  {n} e₁ e₂)

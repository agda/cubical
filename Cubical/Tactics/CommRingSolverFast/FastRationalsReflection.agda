module Cubical.Tactics.CommRingSolverFast.FastRationalsReflection where

open import Cubical.Foundations.Prelude hiding (Type)
open import Cubical.Foundations.Function
open import Agda.Builtin.Reflection hiding (Type)
open import Agda.Builtin.String
open import Agda.Builtin.Nat using () renaming (_==_ to _=ℕ_)
open import Cubical.Reflection.Sugar

open import Cubical.Reflection.Base

open import Cubical.Data.Maybe
open import Cubical.Data.Sigma
open import Cubical.Data.List
open import Cubical.Data.Nat.Literals
open import Cubical.Data.Int.Fast.Base hiding (abs; _-_)
open import Cubical.Data.Int.Fast using (fromNegℤ; fromNatℤ)
open import Cubical.Data.Nat using (ℕ; discreteℕ) renaming (_+_ to _+ℕ_)
open import Cubical.Data.Bool
open import Cubical.Data.Bool.SwitchStatement
open import Cubical.Data.Vec using (Vec) renaming ([] to emptyVec; _∷_ to _∷vec_)

open import Cubical.Relation.Nullary.Base

open import Cubical.Algebra.CommRing

open import Cubical.Tactics.CommRingSolverFast.AlgebraExpression

open import Cubical.Tactics.CommRingSolverFast.OverDecidable

open import Cubical.Tactics.Reflection
open import Cubical.Tactics.Reflection.Variables
open import Cubical.Tactics.Reflection.Utilities
open import Cubical.Tactics.Reflection.Error
open import Cubical.Algebra.CommRing.Instances.Rationals.Fast
open import Cubical.Data.Rationals.Fast as ℚ
open import Cubical.Data.Rationals.Fast.Order as ℚ
open import Cubical.Data.Rationals.Fast.Order.Properties as ℚ
import Cubical.Data.NatPlusOne as NatPlusOne
import Cubical.HITs.SetQuotients as SetQuotient
open import Cubical.Tactics.CommRingSolverFast.RationalsReflection using (doNotUnfoldsℚ)

open DecCommRingSolver ℚCommRing ℚ.discreteℚ ℚCommRing (idCommRingHom ℚCommRing)
import Cubical.Data.NatPlusOne as NPO

open import Cubical.Tactics.CommRingSolverFast.FastRationalsReflectionPre hiding (ℚ!! ; ℚ!!dbg)

dnu : List Name
dnu =
 quote invℚ ∷ quote invℚ₊ ∷ quote ℚ.abs' ∷ quote ℚ.clam∈ℚintervalℙ
  ∷ (quote NPO._+₁_) ∷ (quote NPO._·₊₁_) ∷ (quote NPO.ℕ₊₁→ℕ) ∷ (quote ℚ.ℕ₊₁→ℤ) ∷ doNotUnfoldsℚ

macro
  ℚ!! : Term → TC _
  ℚ!! = solve!-macro false ((quote ℚ._+_) ∷ (quote (ℚ.-_)) ∷ (quote ℚ._·_) ∷ dnu)

  ℚ!!dbg : Term → TC _
  ℚ!!dbg = solve!-macro true ((quote ℚ._+_) ∷ (quote (ℚ.-_)) ∷ (quote ℚ._·_) ∷ dnu)


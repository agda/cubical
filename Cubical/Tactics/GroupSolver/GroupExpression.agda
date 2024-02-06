{-# OPTIONS --safe #-}

module Cubical.Tactics.GroupSolver.GroupExpression where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Relation.Nullary
open import Cubical.Data.Nat as ℕ hiding (_·_)
open import Cubical.Data.List as Li
open import Cubical.Data.Bool
open import Cubical.Data.Sigma

open import Cubical.Algebra.Group

import Cubical.HITs.FreeGroup  as FG
open import Cubical.Algebra.Group.Free
open import Cubical.HITs.FreeGroup.NormalForm

import Agda.Builtin.Reflection as R
open import Cubical.Reflection.Base

open import Agda.Builtin.String
open import Agda.Builtin.Char
open import Agda.Builtin.Nat

infixr 40 _<>_

_<>_ = primStringAppend

private
  variable
    ℓ : Level

module GE (A : Type₀) where
 data GroupExpr : Type₀ where
   η     : A → GroupExpr
   ε     : GroupExpr
   inv   : GroupExpr → GroupExpr
   _·_   : GroupExpr → GroupExpr → GroupExpr

 atoms : GroupExpr → List A
 atoms (η x) = [ x ]
 atoms ε = []
 atoms (inv x) = atoms x
 atoms (x · x₁) = atoms x ++ atoms x₁

 module _ (showA : A → String) where
  showGroupExpr : GroupExpr → String
  showGroupExpr (η x) = showA x
  showGroupExpr ε = "ε"
  showGroupExpr (inv x) = "(" <> showGroupExpr x <> ")⁻¹"
  showGroupExpr (x · x₁) = "(" <> showGroupExpr x <> "·" <> showGroupExpr x₁ <> ")"

 term→FG : GroupExpr → FG.FreeGroup A
 term→FG (η x) = FG.η x
 term→FG ε = FG.ε
 term→FG (inv x) = FG.inv (term→FG x)
 term→FG (x · x₁) = term→FG x FG.· term→FG x₁

module _ (G : Group ℓ) where

 open GroupStr (snd G)

 look : List ⟨ G ⟩ → ℕ → ⟨ G ⟩
 look [] _ = 1g
 look (x ∷ x₂) zero = x
 look (x ∷ x₂) (suc k) = look x₂ k

 open import Cubical.HITs.FreeGroup


 module _ (gs : List ⟨ G ⟩) where
  lk = look gs

  gh = FG.rec {Group = G} lk

  [[_]] : freeGroupGroup ℕ .fst → ⟨ G ⟩
  [[_]] = fst gh

  Solve : (g h : FreeGroup ℕ) → Dec (g ≡ h) → Type ℓ
  Solve g h (yes p) = [[ g ]] ≡ [[ h ]]
  Solve g h (no ¬p) = Lift (List R.ErrorPart)

  solve' : ∀ g h w → Solve g h w
  solve' _ _ (yes p) = cong [[_]] p
  solve' _ _ (no ¬p) = lift [ (R.strErr "L≢R") ]

  solve : ∀ g h → _
  solve g h  = solve' (GE.term→FG ℕ  g) (GE.term→FG ℕ h) (discreteFreeGroup discreteℕ _ _)


module _ (A : Type) (_≟_ : Discrete A) where
 normalizeGroupExpr : GE.GroupExpr A → GE.GroupExpr A
 normalizeGroupExpr =
  foldWord ∘ NF.NF.word ∘ ≟→normalForm _≟_ ∘ GE.term→FG A
  where

  fromAtom : (Bool × A) → GE.GroupExpr A
  fromAtom (false , x) = GE.inv (GE.η x)
  fromAtom (true , x) = GE.η x

  foldWord : [𝟚× A ]  → GE.GroupExpr A
  foldWord [] = GE.ε
  foldWord (x ∷ []) = fromAtom x
  foldWord (x ∷ xs@(_ ∷ _)) = fromAtom x GE.· foldWord xs


digitsToSubscripts : Char → Char
digitsToSubscripts '0' = '₀'
digitsToSubscripts '1' = '₁'
digitsToSubscripts '2' = '₂'
digitsToSubscripts '3' = '₃'
digitsToSubscripts '4' = '₄'
digitsToSubscripts '5' = '₅'
digitsToSubscripts '6' = '₆'
digitsToSubscripts '7' = '₇'
digitsToSubscripts '8' = '₈'
digitsToSubscripts '9' = '₉'
digitsToSubscripts x = x

mkNiceVar : ℕ → String
mkNiceVar k = "x" <>
 primStringFromList (Li.map digitsToSubscripts $ primStringToList $ primShowNat k)

showGEℕ = GE.showGroupExpr ℕ primShowNat
showNormalizedGEℕ = GE.showGroupExpr ℕ mkNiceVar ∘ normalizeGroupExpr ℕ discreteℕ


travGroupExprTC : {A B : Type₀} → (f : A → R.TC B) →
             GE.GroupExpr A → R.TC (GE.GroupExpr B)
travGroupExprTC f = w
 where
 w : GE.GroupExpr _ → R.TC (GE.GroupExpr _)
 w (GE.η x) = (f x) >>= R.returnTC ∘ GE.η
 w GE.ε = R.returnTC GE.ε
 w (GE.inv x) = w x >>= R.returnTC ∘ GE.inv
 w (x GE.· x₁) = do x' ← w x ; x₁' ← w x₁ ; R.returnTC (x' GE.· x₁')


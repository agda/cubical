{-# OPTIONS --safe #-}

module Cubical.Tactics.GroupSolver.GroupExpression where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
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

open import Cubical.Homotopy.Group.Base

infixr 40 _<>_

_<>_ = primStringAppend

private
  variable
    ℓ : Level

module GE (A : Type ℓ) where
 data GroupExpr : Type ℓ where
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



 data π₁GroupExpr : Type ℓ where
   atomGE     : A → π₁GroupExpr
   reflGE     : π₁GroupExpr
   _··_··_   : π₁GroupExpr → π₁GroupExpr → π₁GroupExpr → π₁GroupExpr

 module _ (showA : A → String) where
  showπ₁GroupExpr : π₁GroupExpr → String
  showπ₁GroupExpr (atomGE x) = showA x
  showπ₁GroupExpr reflGE = "refl"
  showπ₁GroupExpr (reflGE ·· x₁ ·· x₂) =
    "(" <> showπ₁GroupExpr x₁ <> "∙" <> showπ₁GroupExpr x₂ <> ")"
  showπ₁GroupExpr (x ·· x₁ ·· reflGE) =
    "(" <> showπ₁GroupExpr x <> "∙'" <> showπ₁GroupExpr x₁ <> ")"
  showπ₁GroupExpr (x ·· x₁ ·· x₂) =
    "(" <> showπ₁GroupExpr x <> "∙∙" <> showπ₁GroupExpr x₁ <> "∙∙" <> showπ₁GroupExpr x₂ <> ")"


module _ (A : Type ℓ) where
 open GE

 termπ₁→GE : π₁GroupExpr (Bool × A) → GroupExpr A
 termπ₁→GE (atomGE (b , a)) = if b then (η a) else inv (η a)
 termπ₁→GE reflGE = ε
 termπ₁→GE (x ·· x₁ ·· x₂) = (termπ₁→GE x · termπ₁→GE x₁) · termπ₁→GE x₂



module Solver (G : Group ℓ) (gs : List ⟨ G ⟩) where

 open GroupStr (snd G)

 open import Cubical.HITs.FreeGroup

 lk = lookupAlways 1g gs

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



-- module _ (A : Type ℓ) (a : A) where
--  open GE

--  termπ₁→Ω : π₁GroupExpr (Bool × (a ≡ a)) → a ≡ a
--  termπ₁→Ω (atomGE (b , p)) = if b then p else (sym p)
--  termπ₁→Ω reflGE = refl
--  termπ₁→Ω (x ·· x₁ ·· x₂) = termπ₁→Ω x ∙∙ termπ₁→Ω x₁ ∙∙ termπ₁→Ω x₂

--  open import Cubical.Homotopy.Group.Base

--  module _ (isGrpA : isGroupoid A) where

--   fromTermπ≡fromTerm∘[[]] : ∀ x → termπ₁→Ω x ≡
--      fst (FG.rec {Group = hGroupoidπ₁ (A , isGrpA) a} (idfun _)) (term→FG _ (termπ₁→GE _ x))
--   fromTermπ≡fromTerm∘[[]] (atomGE (false , snd₁)) = refl
--   fromTermπ≡fromTerm∘[[]] (atomGE (true , snd₁)) = refl
--   fromTermπ≡fromTerm∘[[]] reflGE = refl
--   fromTermπ≡fromTerm∘[[]] (x ·· x₁ ·· x₂) =
--     λ i → doubleCompPath-elim (fromTermπ≡fromTerm∘[[]] x i)
--                               (fromTermπ≡fromTerm∘[[]] x₁ i)
--                               (fromTermπ≡fromTerm∘[[]] x₂ i) i


module πSolver (A : Type ℓ) (isGroupoidA : isGroupoid A) (a : A) l where

 open Solver (hGroupoidπ₁ (A , isGroupoidA) a) l

 open GE

 termπ₁→Ω : π₁GroupExpr (Bool × ℕ) → a ≡ a
 termπ₁→Ω (atomGE (b , k)) = let p = lk k in if b then p else (sym p)
 termπ₁→Ω reflGE = refl
 termπ₁→Ω (x ·· x₁ ·· x₂) = termπ₁→Ω x ∙∙ termπ₁→Ω x₁ ∙∙ termπ₁→Ω x₂

 fromTermπ≡fromTerm∘[[]] : ∀ x → termπ₁→Ω x ≡ [[ (term→FG _ (termπ₁→GE _ x)) ]]
 fromTermπ≡fromTerm∘[[]] (atomGE (false , snd₁)) = refl
 fromTermπ≡fromTerm∘[[]] (atomGE (true , snd₁)) = refl
 fromTermπ≡fromTerm∘[[]] reflGE = refl
 fromTermπ≡fromTerm∘[[]] (x ·· x₁ ·· x₂) =
   λ i → doubleCompPath-elim (fromTermπ≡fromTerm∘[[]] x i)
                             (fromTermπ≡fromTerm∘[[]] x₁ i)
                             (fromTermπ≡fromTerm∘[[]] x₂ i) i


 Solveπ : (g h : π₁GroupExpr (Bool × ℕ)) → Dec (term→FG _ (termπ₁→GE _ g) ≡ term→FG _ (termπ₁→GE _ h)) → Type ℓ
 Solveπ g h (yes p) = termπ₁→Ω g ≡ termπ₁→Ω h
 Solveπ g h (no ¬p) = Lift (List R.ErrorPart)

 solveπ' : ∀ g h w → Solveπ g h w
 solveπ' g h (yes p) =
      fromTermπ≡fromTerm∘[[]] g
   ∙∙ cong [[_]] p
   ∙∙ sym (fromTermπ≡fromTerm∘[[]] h)
 solveπ' _ _ (no ¬p) = lift [ (R.strErr "L≢R") ]

 solveπ : ∀ g h → _
 solveπ g h = solveπ' g h (discreteFreeGroup discreteℕ _ _)



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
digitsToSubscripts = λ where
    '0' → '₀' ; '1' → '₁' ; '2' → '₂' ; '3' → '₃' ; '4' → '₄' ; '5' → '₅'
    '6' → '₆' ; '7' → '₇' ; '8' → '₈' ; '9' → '₉' ; x → x

mkNiceVar : ℕ → String
mkNiceVar k = "𝒙" <>
 primStringFromList (Li.map digitsToSubscripts $ primStringToList $ primShowNat k)

showGEℕ = GE.showGroupExpr ℕ primShowNat
showNormalizedGEℕ = GE.showGroupExpr ℕ mkNiceVar ∘ normalizeGroupExpr ℕ discreteℕ

showπ₁GEℕ = GE.showπ₁GroupExpr (Bool × ℕ)
 λ (b , i) →
   let v = mkNiceVar i
   in if b then v else (v <> "⁻¹")

travGroupExprTC : {A B : Type₀} → (f : A → R.TC B) →
             GE.GroupExpr A → R.TC (GE.GroupExpr B)
travGroupExprTC f = w
 where
 w : GE.GroupExpr _ → R.TC (GE.GroupExpr _)
 w (GE.η x) = (f x) >>= R.returnTC ∘ GE.η
 w GE.ε = R.returnTC GE.ε
 w (GE.inv x) = w x >>= R.returnTC ∘ GE.inv
 w (x GE.· x₁) = do x' ← w x ; x₁' ← w x₁ ; R.returnTC (x' GE.· x₁')

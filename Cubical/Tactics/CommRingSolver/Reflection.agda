{-# OPTIONS --safe #-}
{-
  This is inspired by/copied from:
  https://github.com/agda/agda-stdlib/blob/master/src/Tactic/MonoidSolver.agda
  https://github.com/agda/agda-stdlib/blob/master/src/Tactic/RingSolver.agda

  Boilerplate code for calling the ring solver is constructed automatically
  with agda's reflection features.
-}
module Cubical.Tactics.CommRingSolver.Reflection where

open import Cubical.Foundations.Prelude hiding (Type)
open import Cubical.Functions.Logic

open import Agda.Builtin.Reflection hiding (Type)
open import Agda.Builtin.String

open import Cubical.Reflection.Base

open import Cubical.Data.Maybe
open import Cubical.Data.Sigma
open import Cubical.Data.List
open import Cubical.Data.Nat.Literals
open import Cubical.Data.Int.Base hiding (abs)
open import Cubical.Data.Int using (fromNegℤ; fromNatℤ)
open import Cubical.Data.Nat using (ℕ) renaming (_+_ to _+ℕ_)
open import Cubical.Data.FinData using () renaming (zero to fzero; suc to fsuc)
open import Cubical.Data.Bool
open import Cubical.Data.Bool.SwitchStatement
open import Cubical.Data.Vec using (Vec) renaming ([] to emptyVec; _∷_ to _∷vec_) public

open import Cubical.Tactics.CommRingSolver.AlgebraExpression
open import Cubical.Algebra.CommRing
open import Cubical.Tactics.CommRingSolver.RawAlgebra
open import Cubical.Tactics.CommRingSolver.IntAsRawRing
open import Cubical.Tactics.CommRingSolver.Solver renaming (solve to ringSolve)

private
  variable
    ℓ : Level

  _==_ = primQNameEquality
  {-# INLINE _==_ #-}

  record RingNames : Type where
    field
      is0 : Name → Bool
      is1 : Name → Bool
      is· : Name → Bool
      is+ : Name → Bool
      is- : Name → Bool

  getName : Term → Maybe Name
  getName (con c args) = just c
  getName (def f args) = just f
  getName _            = nothing

  buildMatcher : Name → Maybe Name → Name → Bool
  buildMatcher n nothing  x = n == x
  buildMatcher n (just m) x = n == x or m == x

  findRingNames : Term → TC RingNames
  findRingNames cring =
    let cringStr = varg (def (quote snd) (varg cring ∷ [])) ∷ []
    in do
      0altName ← normalise (def (quote CommRingStr.0r) cringStr)
      1altName ← normalise (def (quote CommRingStr.1r) cringStr)
      ·altName ← normalise (def (quote CommRingStr._·_) cringStr)
      +altName ← normalise (def (quote CommRingStr._+_) cringStr)
      -altName ← normalise (def (quote (CommRingStr.-_)) cringStr)
      returnTC record {
          is0 = buildMatcher (quote CommRingStr.0r) (getName 0altName) ;
          is1 = buildMatcher (quote CommRingStr.1r) (getName 1altName) ;
          is· = buildMatcher (quote CommRingStr._·_) (getName ·altName) ;
          is+ = buildMatcher (quote CommRingStr._+_) (getName +altName) ;
          is- = buildMatcher (quote (CommRingStr.-_)) (getName -altName)
        }

  record VarInfo : Type ℓ-zero where
    field
      varName : String
      varType : Arg Term
      index : ℕ

  {-
    `getLastTwoArgsOf` maps a term 'def n (z₁ ∷ … ∷ zₙ ∷ x ∷ y ∷ [])' to the pair '(x,y)'
    non-visible arguments are ignored.
  -}
  getLastTwoArgsOf : Name → Term → Maybe (Term × Term)
  getLastTwoArgsOf n' (def n xs) =
    if n == n'
    then go xs
    else nothing
      where
      go : List (Arg Term) → Maybe (Term × Term)
      go (varg x ∷ varg y ∷ []) = just (x , y)
      go (x ∷ xs)               = go xs
      go _                      = nothing
  getLastTwoArgsOf n' _ = nothing

  {-
    `getArgs` maps a term 'x ≡ y' to the pair '(x,y)'
  -}
  getArgs : Term → Maybe (Term × Term)
  getArgs = getLastTwoArgsOf (quote PathP)

  private
    solverCallAsTerm : Term → Arg Term → Term → Term → Term
    solverCallAsTerm R varList lhs rhs =
      def
         (quote ringSolve)
         (varg R ∷ varg lhs ∷ varg rhs
           ∷ varList
           ∷ varg (def (quote refl) []) ∷ [])

  solverCallWithLambdas : ℕ → List VarInfo → Term → Term → Term → Term
  solverCallWithLambdas n varInfos R lhs rhs =
    encloseWithIteratedLambda
      (map VarInfo.varName varInfos)
      (solverCallAsTerm R (variableList (rev varInfos)) lhs rhs)
    where
      encloseWithIteratedLambda : List String → Term → Term
      encloseWithIteratedLambda (varName ∷ xs) t = lam visible (abs varName (encloseWithIteratedLambda xs t))
      encloseWithIteratedLambda [] t = t

      variableList : List VarInfo → Arg Term
      variableList [] = varg (con (quote emptyVec) [])
      variableList (varInfo ∷ varInfos)
        = varg (con (quote _∷vec_) (varg (var (VarInfo.index varInfo) []) ∷ (variableList varInfos) ∷ []))

  solverCallByVarIndices : ℕ → List ℕ → Term → Term → Term → Term
  solverCallByVarIndices n varIndices R lhs rhs =
      solverCallAsTerm R (variableList (rev varIndices)) lhs rhs
      where
        variableList : List ℕ → Arg Term
        variableList [] = varg (con (quote emptyVec) [])
        variableList (varIndex ∷ varIndices)
          = varg (con (quote _∷vec_) (varg (var (varIndex) []) ∷ (variableList varIndices) ∷ []))



module pr (R : CommRing ℓ) {n : ℕ} where
  open CommRingStr (snd R)

  0' : Expr ℤAsRawRing (fst R) n
  0' = K 0

  1' : Expr ℤAsRawRing (fst R) n
  1' = K 1

module _ (cring : Term) (names : RingNames) where
  open pr
  open RingNames names

  `0` : List (Arg Term) → Term
  `0` [] = def (quote 0') (varg cring ∷ [])
  `0` (varg fstcring ∷ xs) = `0` xs
  `0` (harg _ ∷ xs) = `0` xs
  `0` _ = unknown

  `1` : List (Arg Term) → Term
  `1` [] = def (quote 1') (varg cring ∷ [])
  `1` (varg fstcring ∷ xs) = `1` xs
  `1` (harg _ ∷ xs) = `1` xs
  `1` _ = unknown

  mutual
    private
      op2 : Name → Term → Term → Term
      op2 op x y = con op (varg (buildExpression x) ∷ varg (buildExpression y) ∷ [])

      op1 : Name → Term → Term
      op1 op x = con op (varg (buildExpression x) ∷ [])

    `_·_` : List (Arg Term) → Term
    `_·_` (harg _ ∷ xs) = `_·_` xs
    `_·_` (varg x ∷ varg y ∷ []) = op2 (quote _·'_) x y
    `_·_` (varg _ ∷ varg x ∷ varg y ∷ []) = op2 (quote _·'_) x y
    `_·_` _ = unknown

    `_+_` : List (Arg Term) → Term
    `_+_` (harg _ ∷ xs) = `_+_` xs
    `_+_` (varg x ∷ varg y ∷ []) = op2 (quote _+'_) x y
    `_+_` (varg _ ∷ varg x ∷ varg y ∷ []) = op2 (quote _+'_) x y
    `_+_` _ = unknown

    `-_` : List (Arg Term) → Term
    `-_` (harg _ ∷ xs) = `-_` xs
    `-_` (varg x ∷ []) = op1 (quote -'_) x
    `-_` (varg _ ∷ varg x ∷ []) = op1 (quote -'_) x

    `-_` _ = unknown

    K' : List (Arg Term) → Term
    K' xs = con (quote K) xs

    finiteNumberAsTerm : ℕ → Term
    finiteNumberAsTerm ℕ.zero = con (quote fzero) []
    finiteNumberAsTerm (ℕ.suc n) = con (quote fsuc) (varg (finiteNumberAsTerm n) ∷ [])

    buildExpression : Term → Term
    buildExpression (var index _) = con (quote ∣) (varg (finiteNumberAsTerm index) ∷ [])
    buildExpression t@(def n xs) =
      switch (λ f → f n) cases
        case is0 ⇒ `0` xs     break
        case is1 ⇒ `1` xs     break
        case is· ⇒ `_·_` xs   break
        case is+ ⇒ `_+_` xs   break
        case is- ⇒ `-_` xs    break
        default⇒ (K' xs)
    buildExpression t@(con n xs) =
      switch (λ f → f n) cases
        case is0 ⇒ `0` xs     break
        case is1 ⇒ `1` xs     break
        case is· ⇒ `_·_` xs   break
        case is+ ⇒ `_+_` xs   break
        case is- ⇒ `-_` xs    break
        default⇒ (K' xs)
    buildExpression t = unknown

  toAlgebraExpression : Maybe (Term × Term) → Maybe (Term × Term)
  toAlgebraExpression nothing = nothing
  toAlgebraExpression (just (lhs , rhs)) = just (buildExpression lhs , buildExpression rhs)

private

  holeMalformedError : {A : Type ℓ} → Term → TC A
  holeMalformedError hole′ = typeError
    (strErr "Something went wrong when getting the variable names in "
     ∷ termErr hole′ ∷ [])

  astExtractionError : {A : Type ℓ} → Term → TC A
  astExtractionError equation = typeError
    (strErr "Error while trying to build ASTs for the equation " ∷
     termErr equation ∷ [])

  variableExtractionError : {A : Type ℓ} → Term → TC A
  variableExtractionError varsToSolve = typeError
    (strErr "Error reading variables to solve " ∷
     termErr varsToSolve ∷
     [])


  mutual
  {- this covers just some common cases and should be refined -}
    adjustDeBruijnIndex : (n : ℕ) → Term → Term
    adjustDeBruijnIndex n (var k args) = var (k +ℕ n) args
    adjustDeBruijnIndex n (def m l) = def m (map (adjustDeBruijnArg n) l)
    adjustDeBruijnIndex n _ = unknown

    adjustDeBruijnArg  : (n : ℕ) → Arg Term → Arg Term
    adjustDeBruijnArg n (arg i (var k args)) = arg i (var (k +ℕ n) args)
    adjustDeBruijnArg n (arg i x) = arg i x

  extractVarIndices : Maybe (List Term) → Maybe (List ℕ)
  extractVarIndices (just ((var index _) ∷ l)) with extractVarIndices (just l)
  ... | just indices = just (index ∷ indices)
  ... | nothing = nothing
  extractVarIndices (just []) = just []
  extractVarIndices _ = nothing

  listToVec : {A : Type ℓ} → (l : List A) → Vec A (length l)
  listToVec [] = emptyVec
  listToVec (x ∷ l) = x ∷vec listToVec l

  getVarsAndEquation : Term → List VarInfo × Term
  getVarsAndEquation t =
    let (rawVars , equationTerm) = extractVars t
        vars = addIndices (length rawVars) (listToVec rawVars)
    in (vars , equationTerm)
    where
          extractVars : Term → List (String × Arg Term) × Term
          extractVars (pi argType (abs varName t)) with extractVars t
          ...                                         | xs , equation
                                                        = (varName , argType) ∷ xs , equation
          extractVars equation = [] , equation

          addIndices : (n : ℕ) → Vec (String × Arg Term) n → List VarInfo
          addIndices ℕ.zero         emptyVec        = []
          addIndices (ℕ.suc countVar) ((varName , argType) ∷vec list) =
            record { varName = varName ; varType = argType ; index = countVar }
            ∷ (addIndices countVar list)

  toListOfTerms : Term → Maybe (List Term)
  toListOfTerms (con c []) = if (c == (quote [])) then just [] else nothing
  toListOfTerms (con c (varg t ∷ varg s ∷ args)) with toListOfTerms s
  ... | just terms = if (c == (quote _∷_)) then just (t ∷ terms) else nothing
  ... | nothing = nothing
  toListOfTerms (con c (harg t ∷ args)) = toListOfTerms (con c args)
  toListOfTerms _ = nothing

  checkIsRing : Term → TC Term
  checkIsRing ring = checkType ring (def (quote CommRing) (varg unknown ∷ []))

  solve-macro : Term → Term → TC Unit
  solve-macro uncheckedCommRing hole =
    do
      commRing ← checkIsRing uncheckedCommRing
      hole′ ← inferType hole >>= normalise
      names ← findRingNames commRing
      (varInfos , equation) ← returnTC (getVarsAndEquation hole′)

      {-
        The call to the ring solver will be inside a lamba-expression.
        That means, that we have to adjust the deBruijn-indices of the variables in 'cring'
      -}
      adjustedCommRing ← returnTC (adjustDeBruijnIndex (length varInfos) commRing)
      just (lhs , rhs) ← returnTC (toAlgebraExpression adjustedCommRing names (getArgs equation))
        where nothing → astExtractionError equation

      let solution = solverCallWithLambdas (length varInfos) varInfos adjustedCommRing lhs rhs
      unify hole solution

  solveInPlace-macro : Term → Term → Term → TC Unit
  solveInPlace-macro cring varsToSolve hole =
    do
      equation ← inferType hole >>= normalise
      names ← findRingNames cring
      just varIndices ← returnTC (extractVarIndices (toListOfTerms varsToSolve))
        where nothing → variableExtractionError varsToSolve

      just (lhs , rhs) ← returnTC (toAlgebraExpression cring names (getArgs equation))
        where nothing → astExtractionError equation

      let solution = solverCallByVarIndices (length varIndices) varIndices cring lhs rhs
      unify hole solution

macro
  solve : Term → Term → TC _
  solve = solve-macro

  solveInPlace : Term → Term → Term → TC _
  solveInPlace = solveInPlace-macro

fromℤ : (R : CommRing ℓ) → ℤ → fst R
fromℤ = scalar

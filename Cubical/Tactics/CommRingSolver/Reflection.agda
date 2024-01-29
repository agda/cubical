{-# OPTIONS --safe #-}
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
open import Cubical.Data.Nat using (ℕ; discreteℕ) renaming (_+_ to _+ℕ_)
open import Cubical.Data.FinData using () renaming (zero to fzero; suc to fsuc)
open import Cubical.Data.Bool
open import Cubical.Data.Bool.SwitchStatement
open import Cubical.Data.Vec using (Vec) renaming ([] to emptyVec; _∷_ to _∷vec_)

open import Cubical.Relation.Nullary.Base

open import Cubical.Algebra.CommRing

open import Cubical.Tactics.CommRingSolver.AlgebraExpression
open import Cubical.Tactics.CommRingSolver.RawAlgebra
open import Cubical.Tactics.CommRingSolver.IntAsRawRing
open import Cubical.Tactics.CommRingSolver.Solver renaming (solve to ringSolve)

open import Cubical.Tactics.Reflection

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
    let cringStr = (def (quote snd) (cring v∷ [])) v∷ []
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
      go (x v∷ y v∷ []) = just (x , y)
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
         (R v∷ lhs v∷ rhs
           v∷ varList
           ∷ (def (quote refl) []) v∷ [])

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
        = varg (con (quote _∷vec_) ((var (VarInfo.index varInfo) []) v∷ (variableList varInfos) ∷ []))

  solverCallByVarIndices : ℕ → List ℕ → Term → Term → Term → Term
  solverCallByVarIndices n varIndices R lhs rhs =
      solverCallAsTerm R (variableList (rev varIndices)) lhs rhs
      where
        variableList : List ℕ → Arg Term
        variableList [] = varg (con (quote emptyVec) [])
        variableList (varIndex ∷ varIndices)
          = varg (con (quote _∷vec_) ((var (varIndex) []) v∷ (variableList varIndices) ∷ []))



module pr (R : CommRing ℓ) {n : ℕ} where
  open CommRingStr (snd R)

  0' : Expr ℤAsRawRing (fst R) n
  0' = K 0

  1' : Expr ℤAsRawRing (fst R) n
  1' = K 1

module _ (cring : Term) (names : RingNames) where
  open pr
  open RingNames names
  private
    Vars = List ℕ

    addWithoutRepetition : ℕ → Vars → Vars
    addWithoutRepetition n (m ∷ l) with discreteℕ n m
    ... | yes p = m ∷ l
    ... | no p = m ∷ addWithoutRepetition n l
    addWithoutRepetition n []      = n ∷ []

    appendWithoutRepetition : Vars → Vars → Vars
    appendWithoutRepetition (x ∷ l) l' = appendWithoutRepetition l (addWithoutRepetition x l')
    appendWithoutRepetition [] l' = l'

  `0` : List (Arg Term) → Term × Vars
  `0` [] = (def (quote 0') (cring v∷ []) , [])
  `0` (fstcring v∷ xs) = `0` xs
  `0` (_ h∷ xs) = `0` xs
  `0` _ = (unknown , [])

  `1` : List (Arg Term) → Term × Vars
  `1` [] = (def (quote 1') (cring v∷ []) , [])
  `1` (fstcring v∷ xs) = `1` xs
  `1` (_ h∷ xs) = `1` xs
  `1` _ = (unknown , [])

  mutual

    private
      op2 : Name → Term → Term → Vars → Term × Vars
      op2 op x y vars = (con op (fst r1 v∷ fst r2 v∷ []) , appendWithoutRepetition (snd r1) (snd r2))
        where
        r1 = buildExpression' x vars
        r2 = buildExpression' y vars

      op1 : Name → Term → Vars → Term × Vars
      op1 op x vars = (con op (fst r1 v∷ []) , snd r1)
        where
        r1 = buildExpression' x vars

    `_·_` : List (Arg Term) → Vars → Term × Vars
    `_·_` (_ h∷ xs) vars = `_·_` xs vars
    `_·_` (x v∷ y v∷ []) vars = op2 (quote _·'_) x y vars
    `_·_` (_ v∷ x v∷ y v∷ []) vars = op2 (quote _·'_) x y vars
    `_·_` _ vars = (unknown , vars)

    `_+_` : List (Arg Term) → Vars → Term × Vars
    `_+_` (_ h∷ xs) vars = `_+_` xs vars
    `_+_` (x v∷ y v∷ []) vars = op2 (quote _+'_) x y vars
    `_+_` (_ v∷ x v∷ y v∷ []) vars = op2 (quote _+'_) x y vars
    `_+_` _ vars = (unknown , vars)

    `-_` : List (Arg Term) → Vars → Term × Vars
    `-_` (_ h∷ xs) vars = `-_` xs vars
    `-_` (x v∷ []) vars = op1 (quote -'_) x vars
    `-_` (_ v∷ x v∷ []) vars = op1 (quote -'_) x vars
    `-_` _ vars = (unknown , vars)

    K' : List (Arg Term) → Vars → Term × Vars
    K' xs vars = (con (quote K) xs , vars)

    finiteNumberAsTerm : ℕ → Term
    finiteNumberAsTerm ℕ.zero = con (quote fzero) []
    finiteNumberAsTerm (ℕ.suc n) = con (quote fsuc) (finiteNumberAsTerm n v∷ [])

    buildExpression : Term → Term
    buildExpression x = fst (buildExpression' x [])


    buildExpression' : Term → Vars → Term × Vars
    buildExpression' (var index _) vars = (con (quote ∣) (finiteNumberAsTerm index v∷ []) , addWithoutRepetition index vars)
    buildExpression' t@(def n xs) vars =
      switch (λ f → f n) cases
        case is0 ⇒ `0` xs         break
        case is1 ⇒ `1` xs         break
        case is· ⇒ `_·_` xs vars  break
        case is+ ⇒ `_+_` xs vars  break
        case is- ⇒ `-_` xs vars   break
        default⇒ (K' xs vars)
    buildExpression' t@(con n xs) vars =
      switch (λ f → f n) cases
        case is0 ⇒ `0` xs         break
        case is1 ⇒ `1` xs         break
        case is· ⇒ `_·_` xs vars  break
        case is+ ⇒ `_+_` xs vars  break
        case is- ⇒ `-_` xs vars   break
        default⇒ (K' xs vars)
    buildExpression' t vars = (unknown , vars)


  toAlgebraExpression : Maybe (Term × Term) → Maybe (Term × Term × Vars)
  toAlgebraExpression nothing = nothing
  toAlgebraExpression (just (lhs , rhs)) = just (fst r1 , fst r2
                                                 , appendWithoutRepetition (snd r1) (snd r2) )
    where
      r1 = buildExpression' lhs []
      r2 = buildExpression' rhs []

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
  toListOfTerms (con c (t v∷ s v∷ args)) with toListOfTerms s
  ... | just terms = if (c == (quote _∷_)) then just (t ∷ terms) else nothing
  ... | nothing = nothing
  toListOfTerms (con c (t h∷ args)) = toListOfTerms (con c args)
  toListOfTerms _ = nothing

  checkIsRing : Term → TC Term
  checkIsRing ring = checkType ring (def (quote CommRing) (unknown v∷ []))

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
      just (lhs , rhs , vars) ← returnTC (toAlgebraExpression adjustedCommRing names (getArgs equation))
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

      just (lhs , rhs) ← get-boundary equation
        where
          nothing
            → typeError(strErr "The CommRingSolver failed to parse the goal"
                               ∷ termErr equation ∷ [])
      just (lhs' , rhs' , vars) ← returnTC (toAlgebraExpression cring names (just (lhs , rhs)))
        where nothing → astExtractionError equation

      let solution = solverCallByVarIndices (length varIndices) varIndices cring lhs' rhs'
      unify hole solution

macro
  solve : Term → Term → TC _
  solve = solve-macro

  solveInPlace : Term → Term → Term → TC _
  solveInPlace = solveInPlace-macro

fromℤ : (R : CommRing ℓ) → ℤ → fst R
fromℤ = scalar

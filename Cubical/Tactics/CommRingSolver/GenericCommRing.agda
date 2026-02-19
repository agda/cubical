module Cubical.Tactics.CommRingSolver.GenericCommRing where

open import Cubical.Foundations.Prelude

open import Agda.Builtin.Reflection hiding (Type)
open import Agda.Builtin.Nat using () renaming (_==_ to _=ℕ_)

open import Cubical.Reflection.Base

open import Cubical.Data.Maybe as Mb
open import Cubical.Data.Sigma
open import Cubical.Data.List
open import Cubical.Data.Nat.Literals
open import Cubical.Data.Int.Base using (ℤ)
open import Cubical.Data.Int using (fromNegℤ; fromNatℤ)
open import Cubical.Data.Nat using (ℕ) renaming (_+_ to _+ℕ_)
open import Cubical.Data.Bool
open import Cubical.Data.Bool.SwitchStatement

open import Cubical.Algebra.CommRing
open import Cubical.Tactics.CommRingSolver.AlgebraExpression

open import Cubical.Tactics.Reflection.Variables
open import Cubical.Tactics.Reflection.Utilities
open import Cubical.Tactics.Reflection.Error

private
 variable
  ℓ : Level



polynomialVariable : Maybe ℕ → Term
polynomialVariable n = con (quote ∣) (finiteNumberAsTerm n v∷ [])


module pr {R : Type ℓ} {n : ℕ} where


  0' : Expr' ℤ R n
  0' = K 0

  1' : Expr' ℤ R n
  1' = K 1



module BE (buildExpression : Term → TC (Template × Vars)) where

 open pr

 `0` : List (Arg Term) → TC (Template × Vars)
 `0` [] = returnTC (((λ _ → def (quote 0') ([])) , []))
 `0` (fstcring v∷ xs) = `0` xs
 `0` (_ h∷ xs) = `0` xs
 `0` something = errorOut something

 `1` : List (Arg Term) → TC (Template × Vars)
 `1` [] = returnTC ((λ _ → def (quote 1') ([])) , [])
 `1` (fstcring v∷ xs) = `1` xs
 `1` (_ h∷ xs) = `1` xs
 `1` something = errorOut something


 op2 : Name → Term → Term → TC (Template × Vars)
 op2 op x y = do
   r1 ← buildExpression x
   r2 ← buildExpression y
   returnTC ((λ ass → con op (fst r1 ass v∷ fst r2 ass v∷ [])) ,
            appendWithoutRepetition (snd r1) (snd r2))

 op1 : Name → Term → TC (Template × Vars)
 op1 op x = do
   r1 ← buildExpression x
   returnTC ((λ ass → con op (fst r1 ass v∷ [])) , snd r1)

 `_·_` : List (Arg Term) → TC (Template × Vars)
 `_·_` (_ h∷ xs) = `_·_` xs
 `_·_` (x v∷ y v∷ []) = op2 (quote _·'_) x y
 `_·_` (_ v∷ x v∷ y v∷ []) = op2 (quote _·'_) x y
 `_·_` ts = errorOut ts

 `_+_` : List (Arg Term) → TC (Template × Vars)
 `_+_` (_ h∷ xs) = `_+_` xs
 `_+_` (x v∷ y v∷ []) = op2 (quote _+'_) x y
 `_+_` (_ v∷ x v∷ y v∷ []) = op2 (quote _+'_) x y
 `_+_` ts = errorOut ts

 `-_` : List (Arg Term) → TC (Template × Vars)
 `-_` (_ h∷ xs) = `-_` xs
 `-_` (x v∷ []) = op1 (quote -'_) x
 `-_` (_ v∷ x v∷ []) = op1 (quote -'_) x
 `-_` ts = errorOut ts


record RingReflectionMatcher : Type where
 field
  mkMatchTermTC : Term → TC
    ((Term → TC (Template × Vars))
        → Term → TC (Maybe (Template × Vars)))



module GenericCommRingReflection where



  record RingNames : Type where
    field
      is0 : Name → Bool
      is1 : Name → Bool
      is· : Name → Bool
      is+ : Name → Bool
      is- : Name → Bool

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
   where

   getName : Term → Maybe Name
   getName (con c args) = just c
   getName (def f args) = just f
   getName _            = nothing

   buildMatcher : Name → Maybe Name → Name → Bool
   buildMatcher n nothing  x = n == x
   buildMatcher n (just m) x = n == x or m == x


  genericCommRingMatchTerm : RingReflectionMatcher
  genericCommRingMatchTerm .RingReflectionMatcher.mkMatchTermTC cring = do
    matchTerm <$> findRingNames cring

   where

   module _ (ringNames : RingNames) (be : (Term → TC (Template × Vars))) where
    open BE be
    open RingNames ringNames

    matchTerm' : Name → List (Arg Term) → TC (Maybe (Template × Vars))
    matchTerm' n xs =
        switch (λ f → f n) cases
      case is0 ⇒ just <$> `0` xs         break
      case is1 ⇒ just <$> `1` xs         break
      case is· ⇒ just <$> `_·_` xs       break
      case is+ ⇒ just <$> `_+_` xs       break
      case is- ⇒ just <$> `-_` xs        break
      default⇒ (returnTC nothing)

    matchTerm : Term → TC (Maybe (Template × Vars))
    matchTerm (con n args) = matchTerm' n args
    matchTerm (def f args) = matchTerm' f args

    -- there should be cases for definitions (with arguments)

    matchTerm _ = returnTC nothing

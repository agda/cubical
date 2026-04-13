{-
  This code contains some helper functions for solvers.
  Variables in the sense of this files are things that are treated like variables by a solver.
  A ring solver might want to treat "f x" in an equation "f x + 0 ≡ f x" like a variable "y".
  During the inspection of the lhs and rhs of an equation, terms like "f x" are found and saved
  and later, indices are assigned to them. These indices will be the indices of the variables
  in the normal forms the solver uses.
-}
module Cubical.Tactics.Reflection.Variables where

open import Cubical.Foundations.Prelude hiding (Type)
open import Cubical.Foundations.Function

open import Agda.Builtin.Reflection hiding (Type)
open import Agda.Builtin.String
open import Agda.Builtin.Float
open import Agda.Builtin.Word
open import Agda.Builtin.Char
open import Agda.Builtin.Nat using () renaming (_==_ to _=ℕ_ ; _<_ to _<ℕ_ ; _*_ to _*ℕ_ ; _+_ to _+ℕ_)

open import Cubical.Reflection.Base
open import Cubical.Data.Bool
open import Cubical.Data.List
open import Cubical.Data.Maybe
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ)

open import Cubical.Tactics.Reflection

private
  variable
    ℓ : Level


Vars = List Term
VarAss = Term → Maybe ℕ
Template = VarAss → Term

private
  _=N_ = primQNameEquality
  _=M_ = primMetaEquality

  _=L_ : Literal → Literal → Bool
  nat n =L nat m = n =ℕ m
  word64 n =L word64 m = primWord64ToNat n =ℕ primWord64ToNat m
  float x =L float y = primFloatEquality x y
  char c =L char c' = primCharEquality c c'
  string s =L string s' = primStringEquality s s'
  name x =L name y = x =N y
  meta x =L meta y = x =M y
  _ =L _ = false

  compareVargs : List (Arg Term) → List (Arg Term) → Bool

  _=T_ : Term → Term → Bool  -- this should be a TC, since it should error out sometimes
  var index args =T var index' args' = (index =ℕ index') and compareVargs args args'
  con c args =T con c' args'   = (c =N c') and compareVargs args args'
  def f args =T def f' args'   = (f =N f') and compareVargs args args'
  lit l =T lit l'              = l =L l'
  meta x args =T meta x' args' = (x =M x') and compareVargs args args'
  _ =T _                       = false  -- this should be fixed

compareVargs [] [] = true
compareVargs (x v∷ l) (x' v∷ l') = (x =T x') and compareVargs l l'
compareVargs (_ h∷ l) (_ h∷ l') = compareVargs l l' -- ignore hargs, not sure this is good
compareVargs _ _ = false

addWithoutRepetition : Term → Vars → Vars
addWithoutRepetition t l@(t' ∷ l') = if (t =T t') then l else t' ∷ addWithoutRepetition t l'
addWithoutRepetition t []      = t ∷ []

appendWithoutRepetition : Vars → Vars → Vars
appendWithoutRepetition (x ∷ l) l' = appendWithoutRepetition l (addWithoutRepetition x l')
appendWithoutRepetition [] l' = l'


-- this can be used to get a map from variables to numbers 0,...,n
indexOf : Term → Vars → Maybe ℕ
indexOf t (t' ∷ l) =
  if (t =T t')
  then just 0
  else map-Maybe (λ k → ℕ.suc k) (indexOf t l)
indexOf t [] = nothing

elemVars : Term → Vars → Bool
elemVars t (t' ∷ l) =
  (t =T t') or (elemVars t l)
elemVars t [] = false

prependWithoutRepetition : Term → Vars → Vars
prependWithoutRepetition t vs =
  t ∷ catMaybes (map (λ t' →  if t =T t' then nothing else just t') vs)

infixr 40 _<>_

_<>_ = primStringAppend


digitsToSubscripts : Char → Char
digitsToSubscripts = λ where
    '0' → '₀' ; '1' → '₁' ; '2' → '₂' ; '3' → '₃' ; '4' → '₄' ; '5' → '₅'
    '6' → '₆' ; '7' → '₇' ; '8' → '₈' ; '9' → '₉' ; x → x

subscriptToℕ : Char → Maybe ℕ
subscriptToℕ = λ where
    '₀' → just 0 ; '₁' → just 1 ; '₂' → just 2 ; '₃' → just 3 ; '₄' → just 5 ; '₅' → just 5
    '₆' → just 6 ; '₇' → just 7 ; '₈' → just 8 ; '₉' → just 9 ; x → nothing




getSubscript : String → Maybe (String × ℕ)
getSubscript s =
 let s' = rev (primStringToList s)
     sbs = takeWhile subscriptToℕ s'
     v = length sbs
 in if (0 <ℕ v) then
       just (primStringFromList (rev (drop (length sbs) s')) , fromBase10rev sbs)
       else nothing
 where
  fromBase10rev : List ℕ → ℕ
  fromBase10rev [] = ℕ.zero
  fromBase10rev (x ∷ xs) = x +ℕ (10 *ℕ fromBase10rev xs)

mkNiceVar' : String → ℕ → String
mkNiceVar' v k = v <>
 primStringFromList (map digitsToSubscripts (primStringToList (primShowNat k)))


mkNiceVar : ℕ → String
mkNiceVar = mkNiceVar' "𝒙"

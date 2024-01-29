{-# OPTIONS --safe #-}
module Cubical.Tactics.Reflection.Variables where

open import Cubical.Foundations.Prelude hiding (Type)

open import Agda.Builtin.Reflection hiding (Type)
open import Agda.Builtin.String
open import Agda.Builtin.Float
open import Agda.Builtin.Word
open import Agda.Builtin.Char
open import Agda.Builtin.Nat using () renaming (_==_ to _=ℕ_)

open import Cubical.Reflection.Base
open import Cubical.Data.Bool
open import Cubical.Data.List
open import Cubical.Data.Maybe
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

indexOf : Term → Vars → Maybe ℕ
indexOf t (t' ∷ l) =
  if (t =T t')
  then just 0
  else map-Maybe (λ k → ℕ.suc k) (indexOf t l)
indexOf t [] = nothing

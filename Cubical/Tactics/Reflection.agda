-- SPDX-License-Identifier: BSD-3-Clause
{-# OPTIONS --safe #-}
module Cubical.Tactics.Reflection where

{- Utilities common to different reflection solvers.

  Most of these are copied/adapted from the 1Lab
-}

open import Cubical.Foundations.Prelude

open import Agda.Builtin.Reflection hiding (Type)

open import Cubical.Data.Bool
open import Cubical.Data.List
open import Cubical.Data.Maybe
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Reflection.Base

private
  variable
    ℓ ℓ' : Level

_<$>_ : ∀ {ℓ ℓ'} {A : Type ℓ}{B : Type ℓ'} → (A → B) → TC A → TC B
f <$> t = t >>= λ x → returnTC (f x)

_<*>_ : ∀ {ℓ ℓ'} {A : Type ℓ}{B : Type ℓ'} → TC (A → B) → TC A → TC B
s <*> t = s >>= λ f → t >>= λ x → returnTC (f x)

wait-for-args : List (Arg Term) → TC (List (Arg Term))
wait-for-type : Term → TC Term

wait-for-type (var x args) = var x <$> wait-for-args args
wait-for-type (con c args) = con c <$> wait-for-args args
wait-for-type (def f args) = def f <$> wait-for-args args
wait-for-type (lam v (abs x t)) = returnTC (lam v (abs x t))
wait-for-type (pat-lam cs args) = returnTC (pat-lam cs args)
wait-for-type (pi (arg i a) (abs x b)) = do
  a ← wait-for-type a
  b ← wait-for-type b
  returnTC (pi (arg i a) (abs x b))
wait-for-type (agda-sort s) = returnTC (agda-sort s)
wait-for-type (lit l) = returnTC (lit l)
wait-for-type (meta x x₁) = blockOnMeta x
wait-for-type unknown = returnTC unknown

wait-for-args [] = returnTC []
wait-for-args (arg i a ∷ xs) =
  (_∷_ <$> (arg i <$> wait-for-type a)) <*> wait-for-args xs

unapply-path : Term → TC (Maybe (Term × Term × Term))
unapply-path red@(def (quote PathP) (l h∷ T v∷ x v∷ y v∷ [])) = do
  domain ← newMeta (def (quote Type) (l v∷ []))
  ty ← returnTC (def (quote Path) (domain v∷ x v∷ y v∷ []))
  debugPrint "tactic" 50
    (strErr "(no reduction) unapply-path: got a " ∷ termErr red
    ∷ strErr " but I really want it to be " ∷ termErr ty ∷ [])
  unify red ty
  returnTC (just (domain , x , y))
unapply-path tm = reduce tm >>= λ where
  tm@(meta _ _) → do
    dom ← newMeta (def (quote Type) [])
    l ← newMeta dom
    r ← newMeta dom
    unify tm (def (quote Type) (dom v∷ l v∷ r v∷ []))
    wait-for-type l
    wait-for-type r
    returnTC (just (dom , l , r))
  red@(def (quote PathP) (l h∷ T v∷ x v∷ y v∷ [])) → do
    domain ← newMeta (def (quote Type) (l v∷ []))
    ty ← returnTC (def (quote Path) (domain v∷ x v∷ y v∷ []))
    debugPrint "tactic" 50
      (strErr "unapply-path: got a " ∷ termErr red
      ∷ strErr " but I really want it to be " ∷ termErr ty ∷ [])
    unify red ty
    returnTC (just (domain , x , y))
  _ → returnTC nothing

{-
  get-boundary maps a term 'x ≡ y' to the pair '(x,y)'
-}
get-boundary : Term → TC (Maybe (Term × Term))
get-boundary tm = unapply-path tm >>= λ where
  (just (_ , x , y)) → returnTC (just (x , y))
  nothing            → returnTC nothing

equation-solver : List Name → (Term -> Term -> TC Term) → Bool → Term → TC Unit
equation-solver don't-Reduce mk-call debug hole =
    withNormalisation false (
    withReduceDefs (false , don't-Reduce) (
    do
      -- | First we normalize the goal
      goal ← inferType hole >>= reduce
      -- | Then we parse the goal into an AST
      just (lhs , rhs) ← get-boundary goal
        where
          nothing
            → typeError(strErr "The functor solver failed to parse the goal"
                               ∷ termErr goal ∷ [])
      -- | Then we invoke the solver
      -- | And we unify the result of the solver with the original hole.
      elhs ← normalise lhs
      erhs ← normalise rhs
      call ← mk-call elhs erhs
      let unify-with-goal = (unify hole call)
      noConstraints (
        if debug
        then unify-with-goal
        else (
        unify-with-goal <|>
        typeError ((strErr "Could not equate the following expressions:\n  "
                  ∷ termErr elhs ∷ strErr "\nAnd\n  " ∷ termErr erhs ∷ []))))))

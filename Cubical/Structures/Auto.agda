{-

Macros (autoDesc, autoIso, autoSNS) for automatically generating structure definitions.

For example:

  autoDesc (λ (X : Type₀) → X → X × ℕ)   ↦   recvar (var , constant ℕ)

We prefer to use the constant structure whenever possible, e.g., [autoDesc (λ (X : Type₀) → ℕ → ℕ)]
is [constant (ℕ → ℕ)] rather than [param ℕ (constant ℕ)].

Writing [auto* (λ X → ⋯)] doesn't seem to work, but [auto* (λ (X : Type ℓ) → ⋯)] does.

-}
{-# OPTIONS --cubical --no-exact-split --safe #-}
module Cubical.Structures.Auto where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order renaming (_≟_ to trichotomy)
open import Cubical.Data.List as List
open import Cubical.Relation.Nullary
open import Cubical.Data.Bool
open import Cubical.Data.Maybe

open import Cubical.Structures.Macro

import Agda.Builtin.Reflection as R

private
  _>>=_ = R.bindTC

  _>>_ : ∀ {ℓ} {B : Type ℓ} → R.TC Unit → R.TC B → R.TC B
  f >> g = f >>= λ _ → g

  infixl 4 _>>=_ _>>_

  liftTC : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
    → (A → B) → R.TC A → R.TC B
  liftTC f m = m >>= (R.returnTC ∘ f)

  mapTC : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
    → (A → R.TC B) → List A → R.TC (List B)
  mapTC f [] = R.returnTC []
  mapTC f (a ∷ as) =
    f a >>= λ b →
    mapTC f as >>= λ bs →
    R.returnTC (b ∷ bs)

  argTC : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
    → (A → R.TC B) → R.Arg A → R.TC (R.Arg B)
  argTC f (R.arg i x) = liftTC (R.arg i) (f x)

  varg : ∀ {ℓ} {A : Type ℓ} → A → R.Arg A
  varg = R.arg (R.arg-info R.visible R.relevant)

  harg : ∀ {ℓ} {A : Type ℓ} → A → R.Arg A
  harg = R.arg (R.arg-info R.hidden R.relevant)

  -- Upper bound on the amount of fuel needed for removeIndex below
  size : R.Term → ℕ
  size (R.var _ []) = 1
  size (R.var x (R.arg _ a ∷ args)) = size a + size (R.var x args)
  size (R.con _ []) = 1
  size (R.con c (R.arg _ a ∷ args)) = size a + size (R.con c args)
  size (R.def _ []) = 1
  size (R.def f (R.arg _ a ∷ args)) = size a + size (R.def f args)
  size (R.lam _ (R.abs _ t)) = suc (size t)
  size (R.pat-lam [] []) = 1
  size (R.pat-lam (R.clause [] t ∷ cs) []) = size t + size (R.pat-lam cs [])
  size (R.pat-lam (R.clause (R.arg _ p ∷ ps) t ∷ cs) []) =
    sizePattern p + size (R.pat-lam (R.clause ps t ∷ cs) [])
    where
    sizePattern : R.Pattern → ℕ
    sizePattern (R.con _ []) = 1
    sizePattern (R.con c (R.arg _ p ∷ ps)) = sizePattern p + sizePattern (R.con c ps)
    sizePattern R.dot = 1
    sizePattern (R.var _) = 1
    sizePattern (R.lit _) = 1
    sizePattern (R.proj _) = 1
    sizePattern R.absurd = 1
  size (R.pat-lam (R.absurd-clause ps ∷ cs) []) = 1
  size (R.pat-lam cs (R.arg _ a ∷ args)) = size a + size (R.pat-lam cs args)
  size (R.pi (R.arg _ a) (R.abs _ b)) = suc (size a + size b)
  size (R.agda-sort (R.set t)) = suc (size t)
  size (R.agda-sort (R.lit _)) = 1
  size (R.agda-sort R.unknown) = 1
  size (R.lit _) = 1
  size (R.meta _ _) = 1
  size R.unknown = 1

  -- Check that de Bruijn index [n] does not appear in a term [t], and decrement indices above [n].
  -- Raises "Bad dependency" if [n] does occur.
  removeIndex : ℕ → R.Term → R.TC R.Term
  removeIndex n t = removeIndex' (size t) n t -- Ought to be possible without fuel...
    where
    countPatternVars : R.Pattern → ℕ
    countPatternVars (R.con c []) = 0
    countPatternVars (R.con c (R.arg _ p ∷ ps)) = countPatternVars p + countPatternVars (R.con c ps)
    countPatternVars R.dot = 0
    countPatternVars (R.var s) = 1
    countPatternVars (R.lit l) = 0
    countPatternVars (R.proj f) = 0
    countPatternVars R.absurd = 0

    countPatternArgsVars : List (R.Arg R.Pattern) → ℕ
    countPatternArgsVars [] = 0
    countPatternArgsVars (R.arg _ p ∷ ps) = countPatternVars p + countPatternArgsVars ps

    removeIndex' : ℕ → ℕ → R.Term → R.TC R.Term
    removeIndex' 0 _ _ = R.typeError (R.strErr "Out of fuel!" ∷ [])
    removeIndex' (suc fuel) n (R.var m args) with trichotomy m n
    ... | lt _ = liftTC (R.var m) (mapTC (argTC (removeIndex' fuel n)) args)
    ... | eq _ = R.typeError [ R.strErr "Bad dependency" ]
    ... | gt _ = liftTC (R.var (predℕ m)) (mapTC (argTC (removeIndex' fuel n)) args)
    removeIndex' (suc fuel) n (R.con c args) = liftTC (R.con c) (mapTC (argTC (removeIndex' fuel n)) args)
    removeIndex' (suc fuel) n (R.def f args) = liftTC (R.def f) (mapTC (argTC (removeIndex' fuel n)) args)
    removeIndex' (suc fuel) n (R.lam v (R.abs s t)) = liftTC (R.lam v ∘ R.abs s) (removeIndex' fuel (suc n) t)
    removeIndex' (suc fuel) n (R.pat-lam cs args) =
      mapTC
        (λ { (R.clause ps body) → liftTC (R.clause ps) (removeIndex' fuel (countPatternArgsVars ps) body)
           ; (R.absurd-clause ps) → R.returnTC (R.absurd-clause ps)
           })
        cs
      >>= λ cs' →
      mapTC (argTC (removeIndex' fuel n)) args >>= λ args' →
      R.returnTC (R.pat-lam cs' args')
    removeIndex' (suc fuel) n (R.pi (R.arg v a) (R.abs s b)) =
      removeIndex' fuel n a >>= λ a' →
      removeIndex' fuel (suc n) b >>= λ b' →
      R.returnTC (R.pi (R.arg v a') (R.abs s b'))
    removeIndex' (suc fuel) n (R.agda-sort (R.set t)) = liftTC (R.agda-sort ∘ R.set) (removeIndex' fuel n t)
    removeIndex' (suc fuel) n (R.agda-sort (R.lit l)) = R.returnTC (R.agda-sort (R.lit l))
    removeIndex' (suc fuel) n (R.agda-sort R.unknown) = R.returnTC (R.agda-sort R.unknown)
    removeIndex' (suc fuel) n (R.lit l) = R.returnTC (R.lit l)
    removeIndex' (suc fuel) n (R.meta x args) = R.blockOnMeta x
    removeIndex' (suc fuel) n R.unknown = R.returnTC R.unknown

  mutual
    -- Build structure descriptor from a term [t], where [n] is the deBruijn index of the type variable
    buildDesc : ℕ → R.Type → R.TC R.Term
    buildDesc n t =
      R.catchTC
        -- Prefer to return constant descriptor if possible
        (removeIndex n t >>= λ _ → R.returnTC (R.con (quote constant) (varg t ∷ [])))
        (buildDesc' n t)

    buildDesc' : ℕ → R.Type → R.TC R.Term
    buildDesc' n A@(R.var x []) with discreteℕ n x
    ... | yes _ = R.returnTC (R.con (quote var) [])
    ... | no _ = R.returnTC (R.con (quote constant) (varg A ∷ []))
    buildDesc' n (R.def Σ (R.arg _ ℓ' ∷ R.arg _ ℓ'' ∷ (R.arg _ A) ∷ (R.arg _ (R.lam _ (R.abs _ B))) ∷ [])) =
      buildDesc n A >>= λ descA →
      R.extendContext (varg (R.def (quote Type) (varg ℓ' ∷ []))) (buildDesc (suc n) B) >>= removeIndex 0 >>= λ descB →
      R.returnTC (R.con (quote Desc._,_) (varg descA ∷ varg descB ∷ []))
    buildDesc' n (R.pi (R.arg (R.arg-info R.visible R.relevant) A@(R.var x [])) (R.abs _ B)) with discreteℕ n x
    ... | yes _ =
      R.extendContext (varg A) (buildDesc (suc n) B) >>= removeIndex 0 >>= λ descB →
      R.returnTC (R.con (quote recvar) (varg descB ∷ []))
    ... | no _ =
      R.extendContext (varg A) (buildDesc (suc n) B) >>= removeIndex 0 >>= λ descB →
      R.returnTC (R.con (quote param) (varg A ∷ varg descB ∷ []))
    buildDesc' n (R.pi (R.arg (R.arg-info R.visible R.relevant) A) (R.abs _ B)) =
      R.extendContext (varg A) (buildDesc (suc n) B) >>= removeIndex 0 >>= λ descB →
      R.returnTC (R.con (quote param) (varg A ∷ varg descB ∷ []))
    buildDesc' n (R.meta x _) = R.blockOnMeta x
    buildDesc' n (R.def (quote Maybe) (R.arg _ _ ∷ R.arg _ A ∷ [])) =
      buildDesc n A >>= λ descA →
      R.returnTC (R.con (quote maybe) (varg descA ∷ []))
    buildDesc' n A = R.returnTC (R.con (quote constant) (varg A ∷ []))

  -- Build structure descriptor from a function [f] with domain [Type ℓ]
  autoDescTerm : R.Term → R.Term → R.TC R.Term
  autoDescTerm ℓ f =
    R.catchTC (R.noConstraints (R.reduce f)) (R.returnTC f) >>= λ where
    (R.lam R.visible (R.abs _ f)) →
      R.extendContext (varg (R.def (quote Type) [ varg ℓ ])) (R.normalise f >>= buildDesc 0) >>=
      removeIndex 0
    _ → R.typeError (R.strErr "Not a function: " ∷ R.termErr f ∷ [])

macro
  autoDesc : R.Term → R.Term → R.TC Unit
  autoDesc t hole =
    R.inferType hole >>= λ H →
    R.checkType R.unknown (R.def (quote Level) []) >>= λ ℓ →
    R.unify (R.def (quote Desc) [ varg ℓ ]) H >>
    autoDescTerm ℓ t >>=
    R.unify hole

  autoIso : R.Term → R.Term → R.TC Unit
  autoIso t hole =
    R.checkType R.unknown (R.def (quote Level) []) >>= λ ℓ →
    R.checkType R.unknown (R.def (quote Desc) [ varg ℓ ]) >>= λ d →
    R.unify (R.def (quote macro-iso) [ varg d ]) hole >>
    autoDescTerm ℓ t >>=
    R.unify d

  autoSNS : R.Term → R.Term → R.TC Unit
  autoSNS t hole =
    R.checkType R.unknown (R.def (quote Level) []) >>= λ ℓ →
    R.checkType R.unknown (R.def (quote Desc) [ varg ℓ ]) >>= λ d →
    R.unify (R.def (quote macro-is-SNS) (varg d ∷ harg R.unknown ∷ harg R.unknown ∷ [])) hole >>
    autoDescTerm ℓ t >>=
    R.unify d

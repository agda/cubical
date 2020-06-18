{-

Macros for automatically generating structure definitions

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

  infixl 4 _>>=_

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

  size : R.Term → ℕ
  size (R.var _ []) = 1
  size (R.var x (R.arg _ a ∷ args)) = size a + size (R.var x args)
  size (R.con _ []) = 1
  size (R.con c (R.arg _ a ∷ args)) = size a + size (R.con c args)
  size (R.def _ []) = 1
  size (R.def f (R.arg _ a ∷ args)) = size a + size (R.def f args)
  size (R.lam _ (R.abs _ t)) = suc (size t)
  size (R.pat-lam cs []) = 1
  size (R.pat-lam cs (R.arg _ a ∷ args)) = size a + size (R.pat-lam cs args)
  size (R.pi (R.arg _ a) (R.abs _ b)) = suc (size a + size b)
  size (R.agda-sort (R.set t)) = suc (size t)
  size (R.agda-sort (R.lit _)) = 1
  size (R.agda-sort R.unknown) = 1
  size (R.lit _) = 1
  size (R.meta _ _) = 1
  size R.unknown = 1

  removeIndex : ℕ → R.Term → R.TC R.Term
  removeIndex n t = removeIndex' (size t) n t
    where
    -- Ought to be possible without fuel...
    removeIndex' : ℕ → ℕ → R.Term → R.TC R.Term
    removeIndex' 0 _ _ = R.typeError (R.strErr "Out of fuel!" ∷ [])
    removeIndex' (suc fuel) n (R.var m args) with trichotomy m n
    ... | lt _ = liftTC (R.var m) (mapTC (argTC (removeIndex' fuel n)) args)
    ... | eq _ = R.typeError [ R.strErr "Bad dependency" ]
    ... | gt _ = liftTC (R.var (predℕ m)) (mapTC (argTC (removeIndex' fuel n)) args)
    removeIndex' (suc fuel) n (R.con c args) = liftTC (R.con c) (mapTC (argTC (removeIndex' fuel n)) args)
    removeIndex' (suc fuel) n (R.def f args) = liftTC (R.def f) (mapTC (argTC (removeIndex' fuel n)) args)
    removeIndex' (suc fuel) n (R.lam v (R.abs s t)) = liftTC (R.lam v ∘ R.abs s) (removeIndex' fuel (suc n) t)
    removeIndex' (suc fuel) n (R.pat-lam cs args) = R.returnTC R.unknown -- fix me
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

  buildDesc : ℕ → R.Type → R.TC R.Term
  buildDesc n A@(R.var x []) with discreteℕ n x
  ... | yes _ = R.returnTC (R.con (quote var) [])
  ... | no _ = R.returnTC (R.con (quote constant) (varg A ∷ []))
  buildDesc n (R.def Σ (R.arg _ ℓ' ∷ R.arg _ ℓ'' ∷ (R.arg _ A) ∷ (R.arg _ (R.lam _ (R.abs _ B))) ∷ [])) =
    buildDesc n A >>= λ descA →
    R.extendContext (varg (R.def (quote Type) (varg ℓ' ∷ []))) (buildDesc (n + 1) B)>>= λ descB →
    removeIndex 0 descB >>= λ descB' →
    R.returnTC (R.con (quote Desc._,_) (varg descA ∷ varg descB' ∷ []))
  buildDesc n (R.pi (R.arg (R.arg-info R.visible R.relevant) A@(R.var x [])) (R.abs _ B)) with discreteℕ n x
  ... | yes _ =
    R.extendContext (varg A) (buildDesc (n + 1) B) >>= λ descB →
    removeIndex 0 descB >>= λ descB' →
    R.returnTC (R.con (quote recvar) (varg descB' ∷ []))
  ... | no _ =
    R.extendContext (varg A) (buildDesc (n + 1) B) >>= λ descB →
    removeIndex 0 descB >>= λ descB' →
    R.returnTC (R.con (quote param) (varg A ∷ varg descB' ∷ []))
  buildDesc n (R.pi (R.arg (R.arg-info R.visible R.relevant) A) (R.abs _ B)) =
    R.extendContext (varg A) (buildDesc (n + 1) B) >>= λ descB →
    removeIndex 0 descB >>= λ descB' →
    R.returnTC (R.con (quote param) (varg A ∷ varg descB' ∷ []))
  buildDesc n (R.meta x _) = R.blockOnMeta x
  buildDesc n (R.def (quote Maybe) (R.arg _ _ ∷ R.arg _ A ∷ [])) =
    buildDesc n A >>= λ descA →
    R.returnTC (R.con (quote maybe) (varg descA ∷ []))
  buildDesc n A = R.returnTC (R.con (quote constant) (varg A ∷ []))

  autoDescTerm : R.Term → R.Term → R.TC R.Term
  autoDescTerm dom t =
    R.catchTC (R.noConstraints (R.reduce t)) (R.returnTC t) >>= λ where
    (R.lam R.visible (R.abs _ t)) →
      R.extendContext (varg dom) (R.normalise t >>= buildDesc 0) >>= removeIndex 0 
    _ → R.typeError (R.strErr "Not a function: " ∷ R.termErr t ∷ [])

macro
  autoDesc : R.Term → R.Term → R.TC Unit
  autoDesc t hole =
    R.inferType hole >>= λ T →
    R.checkType R.unknown (R.def (quote Level) []) >>= λ ℓ →
    R.unify (R.def (quote Desc) [ varg ℓ ]) T >>= λ _ →
    autoDescTerm (R.def (quote Type) [ varg ℓ ]) t >>= R.unify hole

  autoIso : R.Term → R.Term → R.TC Unit
  autoIso t hole =
    R.checkType R.unknown (R.def (quote Level) []) >>= λ ℓ →
    R.checkType R.unknown (R.def (quote Desc) [ varg ℓ ]) >>= λ d →
    R.unify (R.def (quote macro-iso) [ varg d ]) hole >>= λ _ →
    autoDescTerm (R.def (quote Type) [ varg ℓ ]) t >>= R.unify d

  autoSNS : R.Term → R.Term → R.TC Unit
  autoSNS t hole =
    R.checkType R.unknown (R.def (quote Level) []) >>= λ ℓ →
    R.checkType R.unknown (R.def (quote Desc) [ varg ℓ ]) >>= λ d →
    R.unify (R.def (quote macro-is-SNS) (varg d ∷ harg R.unknown ∷ harg R.unknown ∷ [])) hole >>= λ _ →
    autoDescTerm (R.def (quote Type) [ varg ℓ ]) t >>= R.unify d

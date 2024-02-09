{-# OPTIONS --safe #-}

module Cubical.Tactics.GroupSolver.Reflection where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.List
open import Cubical.Data.Maybe

open import Cubical.Reflection.Base
import Agda.Builtin.Reflection as R

quotedMaybe→maybeTerm : R.Term → R.TC (Maybe (R.Term))
quotedMaybe→maybeTerm (R.con (quote nothing) _) = R.returnTC nothing
quotedMaybe→maybeTerm (R.con (quote just) (_ ∷ _ ∷ varg x ∷ [])) = R.returnTC (just x)
quotedMaybe→maybeTerm t =   R.typeError
 (R.termErr t ∷ [(R.strErr "Not a Maybe!")])


quotedList→ListOfTerms : R.Term → R.TC (List (R.Term))
quotedList→ListOfTerms (R.con (quote []) _) = R.returnTC []
quotedList→ListOfTerms (R.con (quote _∷_) (_ ∷ _ ∷ varg x ∷ varg xs ∷ [])) =
 quotedList→ListOfTerms xs >>= (λ xs → R.returnTC (x ∷ xs))
quotedList→ListOfTerms t = R.typeError
 (R.termErr t ∷ [(R.strErr "Not a List!")])

blockIfContainsMeta : R.Term → R.TC Unit

blockIfContainsMeta' : List (R.Arg R.Term) → R.TC Unit
blockIfContainsMeta' [] = R.returnTC _
blockIfContainsMeta' (R.arg i x ∷ x₁) =
 blockIfContainsMeta x >> blockIfContainsMeta' x₁


blockIfContainsMeta (R.var _ args) = blockIfContainsMeta' args
blockIfContainsMeta (R.con _ args) = blockIfContainsMeta' args
blockIfContainsMeta (R.def _ args) = blockIfContainsMeta' args
blockIfContainsMeta (R.lam _ (R.abs s x)) = blockIfContainsMeta x
blockIfContainsMeta (R.pat-lam _ _) = R.typeError [(R.strErr "TODO : blockIfContainsMeta")]
blockIfContainsMeta (R.pi _ _) = R.typeError [(R.strErr "TODO : blockIfContainsMeta")]
blockIfContainsMeta (R.agda-sort _) = R.typeError [(R.strErr "TODO : blockIfContainsMeta")]
blockIfContainsMeta (R.lit l) = R.returnTC _
blockIfContainsMeta (R.meta m _) = R.blockTC (R.blockerMeta m)
blockIfContainsMeta R.unknown = R.returnTC _


catchOrSkip : ∀ {ℓ} {A : Type ℓ} → Bool → R.TC A → R.TC A → R.TC A
catchOrSkip true _ x = x
catchOrSkip false x y = R.catchTC x y


uniqeAtoms : List R.Term → R.TC (List R.Term)
uniqeAtoms [] = R.returnTC []
uniqeAtoms (x ∷ x₁) = do
  notIn ← ensureNotIn x₁
  xs' ← uniqeAtoms x₁
  R.returnTC (if notIn then x ∷ xs' else xs')
 where
 ensureNotIn : List R.Term → R.TC Bool
 ensureNotIn [] = R.returnTC true
 ensureNotIn (x' ∷ xs) =
   R.catchTC ( (R.unify x x' >> R.returnTC false))
             (ensureNotIn xs)


lookT : List R.Term → R.Term → R.TC ℕ
lookT [] _ = R.typeError []
lookT (x ∷ x₂) x₁ =
     R.catchTC ((R.unify x x₁ >> R.returnTC zero))
         (lookT x₂ x₁ >>= R.returnTC ∘ suc)

quoteList : List R.Term → R.Term
quoteList [] = R.con (quote []) []
quoteList (x ∷ x₁) = R.con (quote _∷_)
  (varg x ∷ varg (quoteList x₁) ∷ [])


match2Vargs : List (R.Arg R.Term) → R.TC (R.Term × R.Term)
match2Vargs (harg _ ∷ xs) = match2Vargs xs
match2Vargs (varg t1 ∷ varg t2 ∷ []) = R.returnTC (t1 , t2)
match2Vargs _ = R.typeError []


match3Vargs : List (R.Arg R.Term) → R.TC (R.Term × R.Term × R.Term)
match3Vargs (harg _ ∷ xs) = match3Vargs xs
match3Vargs (varg t1 ∷ varg t2 ∷ varg t3 ∷  []) = R.returnTC (t1 , t2 , t3)
match3Vargs _ = R.typeError []



inferEnds : R.Term → R.TC (R.Type × (R.Term × R.Term))
inferEnds hole = do
  ty ← R.inferType hole
  (eTy , (e0 , e1)) ← pathTypeView ty
  blockIfContainsMeta e0
  blockIfContainsMeta e1

  R.returnTC (eTy , (e0 , e1))
 where
 pathTypeView : R.Term → R.TC (R.Type × (R.Term × R.Term))
 pathTypeView (R.def (quote _≡_) l@(_ ∷ (harg ty) ∷ _)) =
   do e ← match2Vargs l
      R.returnTC (ty , e)
 pathTypeView t = R.typeError (R.strErr "Not a Path Type! : " ∷ [ R.termErr t ])

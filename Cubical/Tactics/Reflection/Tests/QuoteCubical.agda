{-
This module defines several tests for verifying the functionality of cubical term reflection and extraction provided by `Cubical.Tactics.Reflection.QuoteCubical`.
-}

{-# OPTIONS --safe -v 3 #-}
module Cubical.Tactics.Reflection.Tests.QuoteCubical where

import Agda.Builtin.Reflection as R

open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Bool
open import Cubical.Data.Maybe
open import Cubical.Data.Sigma
open import Cubical.Data.List as L

open import Cubical.Reflection.Base hiding (v)


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence

open import Cubical.Tactics.Reflection
open import Cubical.Tactics.Reflection.Utilities


open import Cubical.Tactics.Reflection.Dimensions
open import Cubical.Tactics.Reflection.QuoteCubical
open import Cubical.Tactics.Reflection.CuTerm
open import Cubical.Tactics.Reflection.Error




macro
 extractIExprTest : R.Term → R.Term → R.TC Unit
 extractIExprTest t h = assertNoErr h do
   t' ← extractIExprM t
   R.unify t (IExpr→Term t')

 normIExprTest : R.Term → R.Term → R.TC Unit
 normIExprTest t h = do
   t' ← R.normalise t >>= extractIExprM
   R.unify t (IExpr→Term t')
   R.unify t (IExpr→Term (normIExpr t'))
   wrapError h ("t    : " ∷ₑ IExpr→Term t' ∷nl
                 "norm : " ∷ₑ (IExpr→Term (normIExpr t')) ∷ₑ [])

_ : ResultIs ✓-pass
_ = extractIExprTest i0

_ : ResultIs ✓-pass
_ = extractIExprTest i1



module _ (i j k l : I) where
 _ : ResultIs ✓-pass
 _ = extractIExprTest (~ (j ∧ i ∧ ~ j) ∨ k ∨ (i ∧ ~ i) ∨ (l ∧ i))


 _ : ResultIs ✓-pass
 _ = extractIExprTest (i ∨ ~ i ∨ j ∨ ~ j ∨ k ∨ ~ k)

 _ : ResultIs ✓-pass
 _ = extractIExprTest (~ (i ∨ ~ i ∨ j ∨ ~ j ∨ k ∨ ~ k))

 _ : ResultIs
        ("t    : i ∨ i ∨ (i ∧ i ∧ j) ∨ i ∧ i ∧ k       " ∷
         "norm : i                                     " ∷ [])
 _ = normIExprTest (i ∨ i ∨ (i ∧ i ∧ (j ∨ k)))

 _ : ResultIs
        ("t    : (i ∧ k) ∨ j ∧ k                       " ∷
         "norm : (j ∧ k) ∨ i ∧ k                       " ∷ [])
 _ = normIExprTest ((i ∧ k) ∨ (j ∧ k))



module _ (f : ℕ → I) (i j k l : ℕ) where

 _ : ResultIs ⊘-fail
 _ = extractIExprTest (~ (f j ∧ f i ∧ ~ f j) ∨ (f k) ∨ (f i ∧ ~ f i) ∨ (f l ∧ f i))


macro

 extarctCuTermTest : R.Term → R.Term → R.TC Unit
 extarctCuTermTest t h = assertNoErr h do
  hTy ← R.inferType t >>= wait-for-term >>= R.normalise
  (dim , cu) ← extractCuTermFromNPath hTy t
  (R.unify t (toTerm dim cu))



module gencode (A : Type) (x y z w v : A)
  (p : x ≡ y)(q : y ≡ z)(r : z ≡ w) (s : w ≡ v) where

 _ : ResultIs ✓-pass
 _ = extarctCuTermTest (assoc p q r)

 -- _ : ResultIs ✓-pass
 -- _ = extarctCuTermTest (pentagonIdentity p q r s)

 _ : ResultIs ✓-pass
 _ = extarctCuTermTest (doubleCompPath-filler p q r)



module _ {ℓ ℓ'} {A : Type ℓ} {x y : A} {B : Type ℓ'} (f : A → A → B)
        (p : x ≡ y)
        {u v : A} (q : u ≡ v) where

 _ : ResultIs ✓-pass
 _ = extarctCuTermTest (cong₂Funct f p q)



module E5 (A B C D E F : Type)
  (e₀ : A ≃ B) (e₁ : B ≃ C) (e₂ : C ≃ D) (e₃ : D ≃ E) (e₄ : E ≃ F) where

 _ : ResultIs ✓-pass
 _ = extarctCuTermTest (ua e₀ ∙∙ ua e₁ ∙∙ ua e₂ ∙ ua e₃ ∙ ua e₄)

 _ : ResultIs ✓-pass
 _ = extarctCuTermTest (cong₂Funct (λ A B → List (A × B)) (ua e₁) (ua e₂))


module _ where
 open import Cubical.HITs.S2
 open import Cubical.HITs.Susp

 ss : SquareP (λ u v → Square {A = Susp S²} _ _ _ _) _ _ _ _
 ss i j u v = toSuspPresInvS² (surf u v) i j

 _ : ResultIs ⊘-fail
 _ = extarctCuTermTest ss


module _ where
 open import Cubical.HITs.S1
 open import Cubical.Data.Int

 _ : ResultIs ✓-pass
 _ = extarctCuTermTest (decodeSquare (pos 4))

module _ {ℓ} {A : Type ℓ} {x y z w : A}
           {B C : Type ℓ}
           (f f' : A → B)
         (g : B → B → C)
         (p p' : Path A x y) (q q' : y ≡ z)   (r : z ≡ w) where


 pp = cong₂ g (cong f (p ∙' q)) (cong f' (p' ∙ q'))

 _ : ResultIs ✓-pass
 _ = extarctCuTermTest pp

 _ : ResultIs ✓-pass
 _ = extarctCuTermTest (cong-∙ f p q)




module _ (A B : Type) {x y z : A} (f : A → A → B)
 (p : _≡_ {A = (A → B)} (λ x' → f x' x) (λ x' → f x' y))
 (q : _≡_ {A = (A → B)} (λ x' → f x' y) (λ x' → f x' z))
 where

 _ : ResultIs ✓-pass
 _ = extarctCuTermTest ((p ∙∙ q ∙∙ (sym q)))


module _ (A B : Type) {x y z : A} (f : A → A → B)
 (p : _≡_ {A = ({A} → B)} (λ {x'} → f x' x) (λ {x'} → f x' y))
 (q : _≡_ {A = ({A} → B)} (λ {x'} → f x' y) (λ {x'} → f x' z)) where


 _ : ResultIs ⊘-fail
 _ = extarctCuTermTest (p ∙∙ q ∙∙ sym q)

module _ (A B : Type) {x y z : A} (p : x ≡ y) (q : y ≡ z) (r : x ≡ z) where

 w w' : Path (B → A) (λ _ → x) λ _ → z
 w i = λ _ → (p ∙ q) i
 w' = cong const p ∙ cong const q

 w≡w'' : w ≡ w'
 w≡w'' = refl



 _ : ResultIs ⊘-fail
 _ = extarctCuTermTest w

 _ : ResultIs ✓-pass
 _ = extarctCuTermTest w'


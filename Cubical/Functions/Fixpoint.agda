{-
  Definition of function fixpoint and Kraus' lemma
-}
{-# OPTIONS --safe #-}
module Cubical.Functions.Fixpoint where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws

private
  variable
    ℓ : Level
    A : Type ℓ

Fixpoint : (A → A) → Type _
Fixpoint {A = A} f = Σ A (λ x → f x ≡ x)

fixpoint : {f : A → A} → Fixpoint f → A
fixpoint = fst

fixpointPath : {f : A → A} → (p : Fixpoint f) → f (fixpoint p) ≡ fixpoint p
fixpointPath = snd

-- Kraus' lemma
-- a version not using cubical features can be found at
-- https://www.cs.bham.ac.uk/~mhe/GeneralizedHedberg/html/GeneralizedHedberg.html#21576
2-Constant→isPropFixpoint : (f : A → A) → 2-Constant f → isProp (Fixpoint f)
2-Constant→isPropFixpoint f fconst (x , p) (y , q) i = s i , t i where
  noose : ∀ x y → f x ≡ f y
  noose x y = sym (fconst x x) ∙ fconst x y
  -- the main idea is that for any path p, cong f p does not depend on p
  -- but only on its endpoints and the structure of 2-Constant f
  KrausInsight : ∀ {x y} → (p : x ≡ y) → noose x y ≡ cong f p
  KrausInsight {x} = J (λ y p → noose x y ≡ cong f p) (lCancel (fconst x x))
  -- Need to solve for a path s : x ≡ y, such that:
  -- transport (λ i → cong f s i ≡ s i) p ≡ q
  s : x ≡ y
  s = sym p ∙∙ noose x y ∙∙ q
  t' : PathP (λ i → noose x y i ≡ s i) p q
  t' i j = doubleCompPath-filler (sym p) (noose x y) q j i
  t : PathP (λ i → cong f s i ≡ s i) p q
  t = subst (λ kraus → PathP (λ i → kraus i ≡ s i) p q) (KrausInsight s) t'

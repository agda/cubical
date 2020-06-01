{-
  Definition of function fixpoint and Kraus' lemma
-}
{-# OPTIONS --cubical --safe #-}
module Cubical.Functions.Fixpoint where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path

module _ {ℓ} {A : Type ℓ} where
  Fixpoint : (A → A) → Type ℓ
  Fixpoint f = Σ A (λ x → f x ≡ x)

  fixpoint : {f : A → A} → Fixpoint f → A
  fixpoint = fst

  fixpointPath : {f : A → A} → (p : Fixpoint f) → f (fixpoint p) ≡ fixpoint p
  fixpointPath = snd

  2-Constant→isPropFixpoint : (f : A → A) → 2-Constant f → isProp (Fixpoint f)
  2-Constant→isPropFixpoint f connection (x , p) (y , q) i = s i , t i where
    noose : ∀ x y → f x ≡ f y
    noose x y = sym (connection x x) ∙ connection x y
    -- the main idea is that for any path p, cong f p does not depend p
    -- but only on its endpoints and the structure of 2-Constant f
    KrausLemma : ∀ {x y} → (p : x ≡ y) → noose x y ≡ cong f p
    KrausLemma {x} = J (λ y p → noose x y ≡ cong f p) (lCancel (connection x x))
    -- Need to solve for a path s : x ≡ y, such that:
    -- transport (λ i → cong f s i ≡ s i) p ≡ q
    s : x ≡ y
    s = sym p ∙∙ noose x y ∙∙ q
    t' : PathP (λ i → p i ≡ q i) (noose x y) s
    t' = doubleCompPath-filler (sym p) (noose x y) q
    t : PathP (λ i → cong f s i ≡ s i) p q
    t i j = subst (λ noose → PathP (λ i → p i ≡ q i) noose s) (KrausLemma s) t' j i

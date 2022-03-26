{-# OPTIONS --cubical --guardedness #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism renaming (Iso to _≅_)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Nat

module Cubical.Data.W where

open _≅_

private
  variable
    ℓX ℓS ℓP : Level

module Types {X : Type ℓX} (S : X → Type ℓS) (P : ∀ x → S x → Type ℓP) (inX : ∀ x (s : S x) → P x s → X) where
  data W : (x : X) → Type (ℓ-max ℓX (ℓ-max ℓS ℓP)) where
    node : ∀ {x} → (s : S x) → (subtree : (p : P x s) → W (inX x s p)) → W x

  Subtree : ∀ {x} → (s : S x) → Type (ℓ-max (ℓ-max ℓX ℓS) ℓP)
  Subtree {x} s = (p : P x s) → W (inX x s p)

  RepW : (x : X) → Type (ℓ-max (ℓ-max ℓX ℓS) ℓP)
  RepW x = Σ[ s ∈ S x ] Subtree s

open Types public

module _ {X : Type ℓX} {S : X → Type ℓS} {P : ∀ x → S x → Type ℓP} {inX : ∀ x (s : S x) → P x s → X} where

  getShape : ∀ {x} → W S P inX x → S x
  getShape (node s subtree) = s

  getSubtree : ∀ {x} → (w : W S P inX x) → (p : P x (getShape w)) → W S P inX (inX x (getShape w) p)
  getSubtree (node s subtree) = subtree

  isoRepW : (x : X) → W S P inX x ≅ RepW S P inX x
  fun (isoRepW x) (node s subtree) = s , subtree
  inv (isoRepW x) (s , subtree) = node s subtree
  rightInv (isoRepW x) (s , subtree) = refl
  leftInv (isoRepW x) (node s subtree) = refl

  equivRepW : (x : X) → W S P inX x ≃ RepW S P inX x
  equivRepW x = isoToEquiv (isoRepW x)

  pathRepW : (x : X) → W S P inX x ≡ RepW S P inX x
  pathRepW x = ua (equivRepW x)

  isPropW : (∀ x → isProp (S x)) → ∀ x → isProp (W S P inX x)
  isPropW isPropS x (node s subtree) (node s' subtree') =
    cong₂ node (isPropS x s s') (toPathP (funExt λ p → isPropW isPropS _ _ (subtree' p)))

  isOfHLevelSuc-W : (n : HLevel) → (∀ x → isOfHLevel (suc n) (S x)) → ∀ x → isOfHLevel (suc n) (W S P inX x)
  isOfHLevelSuc-W zero isHS x = isPropW isHS x
  isOfHLevelSuc-W (suc n) isHS x = subst (isOfHLevel (2 + n)) (sym (pathRepW x))
    λ rw@(s , subtree) rw'@(s' , subtree') → subst (isOfHLevel (suc n)) (ΣPathTransport≡PathΣ rw rw') {!This doesn't help.!}

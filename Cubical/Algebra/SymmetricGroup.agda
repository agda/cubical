{-# OPTIONS --cubical --safe #-}
module Cubical.Algebra.SymmetricGroup where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ ; suc ; zero)
open import Cubical.Data.Fin using (Fin ; isSetFin)
open import Cubical.Data.Empty
open import Cubical.Relation.Nullary using (¬_)



open import Cubical.Structures.Group

private
  variable
    ℓ ℓ' : Level


private
  lemma : ∀ (X : Type ℓ) → isSet X → isSet (X ≃ X)
  lemma X X-isSet = isOfHLevelΣ 2 (isOfHLevelΠ 2 (λ _ → X-isSet)) λ f → isProp→isSet (isPropIsEquiv f)

infixr 20 _∘_

_∘_ : {A B C : Type ℓ} → B ≃ C → A ≃ B → A ≃ C
g ∘ f = compEquiv f g

∘-assoc : {A B C D : Type ℓ} (h : C ≃ D) (g : B ≃ C) (f : A ≃ B)
        → h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f
∘-assoc h g f = equivEq _ _ refl

-- Move computation rules of equivalences to Cubical.Foundations.Equiv?

compEquivEquivId : {A B : Type ℓ} (e : A ≃ B) → compEquiv e (idEquiv B) ≡ e
compEquivEquivId e = equivEq _ _ refl

invEquiv-is-rinv : {A B : Type ℓ} (e : A ≃ B) → compEquiv e (invEquiv e) ≡ idEquiv A
invEquiv-is-rinv e = equivEq _ _ (funExt (secEq e))

invEquiv-is-linv : {A B : Type ℓ} (e : A ≃ B) → compEquiv (invEquiv e) e ≡ idEquiv B
invEquiv-is-linv e = equivEq _ _ (funExt (retEq e))

Symmetric-Group : (X : Type ℓ) → isSet X → Groups
Symmetric-Group X isSetX =
  (X ≃ X) ,
  _∘_ ,
  (lemma X isSetX , ∘-assoc) ,
  idEquiv X , (λ f → compEquivIdEquiv f , compEquivEquivId f) , λ f → invEquiv f , invEquiv-is-linv f , invEquiv-is-rinv f

-- Finite symmetrics groups
Sym : ℕ → Groups
Sym n = Symmetric-Group (Fin n) isSetFin

-- Find where this is defined :
_≢_ : {X : Type ℓ} → X → X → Type ℓ
x ≢ y = ¬ (x ≡ y)


℘ : Type ℓ → Type (ℓ-suc ℓ)
℘ {ℓ} X = X → hProp ℓ

supp : {X : Type ℓ} {P : isSet X} → ⟨ Symmetric-Group X P ⟩ → ℘ X
supp {P = P} f x = (equivFun f x ≢ x) , isPropΠ λ _ → isProp⊥

-- TODO: In order to do this easily we have to develop a theory of sets

 

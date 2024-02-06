{-

This file contains quotient groups

-}
{-# OPTIONS --safe #-}
module Cubical.Algebra.Group.QuotientGroup where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.GroupoidLaws hiding (assoc)
open import Cubical.Data.Sigma
open import Cubical.HITs.SetQuotients.Base renaming (_/_ to _/s_)
open import Cubical.HITs.SetQuotients.Properties
open import Cubical.Relation.Binary.Base

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Properties
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Subgroup

open import Cubical.Tactics.GroupSolver.Solver

private
  variable
    ℓ : Level

module _ (G' : Group ℓ) (H' : Subgroup G') (Hnormal : isNormal H') where

  open BinaryRelation
  open isSubgroup (snd H')
  open GroupStr (snd G')
  open GroupTheory G'
  private
    G = ⟨ G' ⟩

  _~_ : G → G → Type ℓ
  x ~ y = x · inv y ∈ ⟪ H' ⟫

  isRefl~ : isRefl _~_
  isRefl~ x = subst-∈ ⟪ H' ⟫ (sym (·InvR x)) id-closed

  G/H : Type ℓ
  G/H = G /s _~_

  1/H : G/H
  1/H = [ 1g ]

  _·/H_ : G/H → G/H → G/H
  _·/H_ = setQuotBinOp isRefl~ isRefl~ _·_
   (λ a a' b b' haa' hbb' → subst-∈ ⟪ H' ⟫
     (solveGroup G')
     (Hnormal a' _ (op-closed  (·CommNormalSubgroup H' Hnormal haa') hbb')))


  inv/H : G/H → G/H
  inv/H = setQuotUnaryOp inv
    λ _ a' haa' →  subst-∈ ⟪ H' ⟫ (solveGroup G') (Hnormal (inv a') _ (inv-closed haa'))

  ·/H-assoc : (a b c : G/H) → (a ·/H (b ·/H c)) ≡ ((a ·/H b) ·/H c)
  ·/H-assoc = elimProp3 (λ x y z → squash/ _ _) λ x y z → cong [_] (·Assoc x y z)

  ·/H-rid : (a : G/H) → (a ·/H 1/H) ≡ a
  ·/H-rid = elimProp (λ x → squash/ _ _) λ x → cong [_] (·IdR x)

  ·/H-invr : (a : G/H) → (a ·/H inv/H a) ≡ 1/H
  ·/H-invr = elimProp (λ x → squash/ _ _) λ x → cong [_] (·InvR x)

  asGroup : Group ℓ
  asGroup = makeGroup-right 1/H _·/H_ inv/H squash/ ·/H-assoc ·/H-rid ·/H-invr


_/_ : (G : Group ℓ) → (H : NormalSubgroup G) → Group ℓ
G / H = asGroup G (H .fst) (H .snd)

[_]/G : {G : Group ℓ} {H : NormalSubgroup G} → ⟨ G ⟩ → ⟨ G / H ⟩
[ x ]/G = [ x ]

-- Quotienting by a trivial subgroup
module _ {G' : Group ℓ} (H' : NormalSubgroup G')
         (contrH : (x y : fst G') → _~_ G' (fst H') (snd H') x y → x ≡ y) where
  private
    -- open isSubgroup (snd H')
    open GroupStr (snd G')
    open GroupTheory G'
    G = fst G'
    G/H' = fst (G' / H')

    Code : (g : G) → G/H' → hProp ℓ
    Code g =
      elim (λ _ → isSetHProp)
        (λ a → (g ≡ a) , is-set _ _)
        λ a b r → Σ≡Prop (λ _ → isPropIsProp) (cong (g ≡_) (contrH a b r))

    decode : (g : G) (x : G/H') → [ g ] ≡ x → Code g x .fst
    decode g x = J (λ x _ → Code g x .fst) refl

  trivialRel→elimPath : {g h : G} → Path G/H' [ g ] [ h ] → g ≡ h
  trivialRel→elimPath {g = g} {h = h} = decode g [ h ]

  trivialRelIso : GroupIso G' (G' / H')
  Iso.fun (fst trivialRelIso) g = [ g ]
  Iso.inv (fst trivialRelIso) =
    rec is-set (λ g → g) contrH
  Iso.rightInv (fst trivialRelIso) =
    elimProp (λ _ → squash/ _ _) λ _ → refl
  Iso.leftInv (fst trivialRelIso) _ = refl
  snd trivialRelIso =
    makeIsGroupHom λ _ _ → refl

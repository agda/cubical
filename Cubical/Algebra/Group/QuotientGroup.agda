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
  isRefl~ x = subst-∈ ⟪ H' ⟫ (sym (invr x)) id-closed

  G/H : Type ℓ
  G/H = G /s _~_

  1/H : G/H
  1/H = [ 1g ]

  _·/H_ : G/H → G/H → G/H
  x ·/H y = setQuotBinOp isRefl~ isRefl~ _·_ rem x y
   where
   rem : (a a' b b' : G)
       → a · inv a' ∈ ⟪ H' ⟫
       → b · inv b' ∈ ⟪ H' ⟫
       → (a · b) · inv (a' · b') ∈ ⟪ H' ⟫
   rem a a' b b' haa' hbb' = subst-∈ ⟪ H' ⟫ (cong (_ ·_) (sym (invDistr _ _))) rem5
     where
     rem1 : (inv a' · a) · b · inv b' ∈ ⟪ H' ⟫
     rem1 = ·CommNormalSubgroup H' Hnormal
              (op-closed  hbb' (·CommNormalSubgroup H' Hnormal haa'))

     rem2 : ((inv a' · a) · b) · inv b' ∈ ⟪ H' ⟫
     rem2 = subst-∈ ⟪ H' ⟫ (assoc _ _ _) rem1

     rem3 : inv b' · (inv a' · a) · b ∈ ⟪ H' ⟫
     rem3 = ·CommNormalSubgroup H' Hnormal rem2

     rem4 : (inv b' · inv a') · (a · b) ∈ ⟪ H' ⟫
     rem4 = subst-∈ ⟪ H' ⟫ (cong (inv b' ·_) (sym (assoc _ _ _)) ∙ assoc _ _ _) rem3

     rem5 : (a · b) · inv b' · inv a' ∈ ⟪ H' ⟫
     rem5 = ·CommNormalSubgroup H' Hnormal rem4

  inv/H : G/H → G/H
  inv/H = setQuotUnaryOp inv rem
    where
    rem : (a a' : G) → a · inv a' ∈ ⟪ H' ⟫ → inv a · inv (inv a') ∈ ⟪ H' ⟫
    rem a a' haa' = subst-∈ ⟪ H' ⟫ (cong (inv a ·_) (sym (invInv a'))) rem1
      where
      ha'a : a' · inv a ∈ ⟪ H' ⟫
      ha'a = subst-∈ ⟪ H' ⟫ (invDistr a (inv a') ∙ cong (_· inv a) (invInv a')) (inv-closed haa')

      rem1 : inv a · a' ∈ ⟪ H' ⟫
      rem1 = ·CommNormalSubgroup H' Hnormal ha'a

  ·/H-assoc : (a b c : G/H) → (a ·/H (b ·/H c)) ≡ ((a ·/H b) ·/H c)
  ·/H-assoc = elimProp3 (λ x y z → squash/ _ _) λ x y z → cong [_] (assoc x y z)

  ·/H-rid : (a : G/H) → (a ·/H 1/H) ≡ a
  ·/H-rid = elimProp (λ x → squash/ _ _) λ x → cong [_] (rid x)

  ·/H-invr : (a : G/H) → (a ·/H inv/H a) ≡ 1/H
  ·/H-invr = elimProp (λ x → squash/ _ _) λ x → cong [_] (invr x)

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

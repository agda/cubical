{-

This file contains quotient groups

-}
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.Group.QuotientGroup where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.GroupoidLaws hiding (assoc)
open import Cubical.Data.Sigma
-- open import Cubical.HITs.PropositionalTruncation
open import Cubical.HITs.SetQuotients.Base
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

module _ (G' : Group {ℓ}) (H' : Subgroup G') (Hnormal : isNormal H') where

  open BinaryRelation
  open isSubgroup (snd H')
  open GroupStr (snd G')
  open GroupTheory G'
  private
    G = ⟨ G' ⟩

  _~_ : G → G → Type ℓ
  x ~ y = x · inv y ∈ ⟪ H' ⟫

  -- TODO: upstream
  foo : (x y : G) → x · y ∈ ⟪ H' ⟫ → y · x ∈ ⟪ H' ⟫
  foo x y Hxy = subst (_∈ ⟪ H' ⟫) h2 h1
    where
    h1 : inv x · (x · y) · inv (inv x) ∈ ⟪ H' ⟫
    h1 = Hnormal (inv x) _ Hxy

    h2 : inv x · (x · y) · inv (inv x) ≡ y · x
    h2 = inv x · (x · y) · inv (inv x) ≡⟨ assoc _ _ _ ⟩
         (inv x · x · y) · inv (inv x) ≡⟨ (λ i → assoc (inv x) x y i · invInv x i) ⟩
         ((inv x · x) · y) · x         ≡⟨ cong (λ z → (z · y) · x) (invl x) ⟩
         (1g · y) · x                  ≡⟨ cong (_· x) (lid y) ⟩
         y · x ∎

  isRefl~ : isRefl _~_
  isRefl~ x = subst (_∈ ⟪ H' ⟫) (sym (invr x)) id-closed

  G/H : Type ℓ
  G/H = G / (λ x y → x · inv y ∈ ⟪ H' ⟫)

  1/H : G/H
  1/H = [ 1g ]

  _·/H_ : G/H → G/H → G/H
  x ·/H y = setQuotBinOp isRefl~ _·_
                {!!}
--                (λ a a' b b' haa' hbb' → subst (_∈ ⟪ H' ⟫) {!!} (op-closed hbb' haa'))
                x y
   where
   rem : (a a' b b' : G) → a · (b · inv b') · inv a' ≡ (a · b) · inv (a' · b')
   rem a a' b b' =
     a · (b · inv b') · inv a' ≡⟨ {!assoc a (b · inv b') (inv a)!} ⟩
     {!!} ≡⟨ {!!} ⟩
     {!!} ≡⟨ {!!} ⟩
     {!!} ≡⟨ {!!} ⟩
     {!!} ≡⟨ {!!} ⟩
     (a · b) · inv b' · inv a' ≡⟨ cong ((a · b) ·_) (sym (invDistr _ _)) ⟩
     (a · b) · inv (a' · b') ∎

  inv/H : G/H → G/H
  inv/H = setQuotUnaryOp inv λ a a' haa' → subst (_∈ ⟪ H' ⟫) (cong (inv a ·_) (sym (invInv a'))) (foo _ _ (ha'a a' a haa'))
     where
     ha'a : (a' a : G) → (haa' : a · inv a' ∈ ⟪ H' ⟫) → a' · inv a ∈ ⟪ H' ⟫
     ha'a a' a haa' = subst (_∈ ⟪ H' ⟫) (invDistr a (inv a') ∙ cong (_· inv a) (invInv a')) (inv-closed haa')

  asGroup : Group {ℓ}
  asGroup = makeGroup-right {A = G/H} 1/H _·/H_ inv/H squash/ {!!} {!!} {!!}

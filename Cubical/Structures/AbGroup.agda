{-# OPTIONS --cubical --safe #-}
module Cubical.Structures.AbGroup where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Foundations.SIP renaming (SNS-PathP to SNS)

open import Cubical.Structures.NAryOp
open import Cubical.Structures.Group hiding (⟨_⟩)

private
  variable
    ℓ : Level

abelian-group-axioms : (X : Type ℓ) → raw-group-structure X → Type ℓ
abelian-group-axioms X _·_ = group-axioms X _·_ ×
                             ((x y : X) → x · y ≡ y · x)

abelian-group-structure : Type ℓ → Type ℓ
abelian-group-structure = add-to-structure raw-group-structure abelian-group-axioms

AbGroup : Type (ℓ-suc ℓ)
AbGroup {ℓ} = TypeWithStr ℓ abelian-group-structure

abelian-group-iso : StrIso abelian-group-structure ℓ
abelian-group-iso = add-to-iso (nAryFunIso 2) abelian-group-axioms

abelian-group-axioms-isProp : (X : Type ℓ)
                           → (s : raw-group-structure X)
                           → isProp (abelian-group-axioms X s)
abelian-group-axioms-isProp X _·_ = isPropΣ (group-axioms-isProp X _·_)
                                    λ { ((isSetX , _) , _) → isPropΠ2 λ _ _ → isSetX _ _}

abelian-group-is-SNS : SNS {ℓ} abelian-group-structure abelian-group-iso
abelian-group-is-SNS = add-axioms-SNS _ abelian-group-axioms-isProp raw-group-is-SNS

AbGroupPath : (M N : AbGroup {ℓ}) → (M ≃[ abelian-group-iso ] N) ≃ (M ≡ N)
AbGroupPath = SIP abelian-group-is-SNS

-- Abelian group is group

AbGroup→Group : AbGroup {ℓ} → Group
AbGroup→Group (G , _·_ , isGroup , ·comm) = G , _·_ , isGroup

-- Abelian group extractors

⟨_⟩ : AbGroup {ℓ} → Type ℓ
⟨ G , _ ⟩ = G

module _ (G : AbGroup {ℓ}) where

  abgroup-operation = group-operation (AbGroup→Group G)

  abgroup-is-set = group-is-set (AbGroup→Group G)

  abgroup-assoc = group-assoc (AbGroup→Group G)

  abgroup-id = group-id (AbGroup→Group G)

  abgroup-rid = group-rid (AbGroup→Group G)

  abgroup-lid = group-lid (AbGroup→Group G)

  abgroup-inv = group-inv (AbGroup→Group G)

  abgroup-rinv = group-rinv (AbGroup→Group G)

  abgroup-linv = group-linv (AbGroup→Group G)

module abgroup-operation-syntax where

  abgroup-operation-syntax : (G : AbGroup {ℓ}) → ⟨ G ⟩ → ⟨ G ⟩ → ⟨ G ⟩
  abgroup-operation-syntax G = abgroup-operation G
  infixr 20 abgroup-operation-syntax
  syntax abgroup-operation-syntax G x y = x ·⟨ G ⟩ y

open abgroup-operation-syntax

abgroup-comm : (G : AbGroup {ℓ}) (x y : ⟨ G ⟩) → x ·⟨ G ⟩ y ≡ y ·⟨ G ⟩ x
abgroup-comm (_ , _ , _ , P) = P

-- AbGroup ·syntax

module abgroup-·syntax (G : AbGroup {ℓ}) where
  open group-·syntax (AbGroup→Group G) public

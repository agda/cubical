{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Structures.Group where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Foundations.SIP renaming (SNS-PathP to SNS)

open import Cubical.Data.Sigma

open import Cubical.Structures.Macro
open import Cubical.Structures.NAryOp
open import Cubical.Structures.Pointed
open import Cubical.Structures.Semigroup hiding (⟨_⟩)
open import Cubical.Structures.Monoid hiding (⟨_⟩)

open Iso

private
  variable
    ℓ : Level

record IsGroup {G : Type ℓ} (0g : G) (_+_ : G → G → G) (-_ : G → G) : Type ℓ where

  constructor isgroup

  field
    isMonoid  : IsMonoid 0g _+_
    inverse   : (x : G) → (x + (- x) ≡ 0g) × ((- x) + x ≡ 0g)

  open IsMonoid isMonoid public

  infixl 6 _-_

  _-_ : G → G → G
  x - y = x + (- y)

  invl : (x : G) → (- x) + x ≡ 0g
  invl x = inverse x .snd

  invr : (x : G) → x + (- x) ≡ 0g
  invr x = inverse x .fst

  -- uniqueness of inverse?

record Group : Type (ℓ-suc ℓ) where

  constructor group

  field
    Carrier : Type ℓ
    0g      : Carrier
    _+_     : Carrier → Carrier → Carrier
    -_      : Carrier → Carrier
    isGroup : IsGroup 0g _+_ -_

  infix  8 -_
  infixl 7 _+_

  open IsGroup isGroup public

-- Extractor for the carrier type
⟨_⟩ : Group → Type ℓ
⟨_⟩ = Group.Carrier

-- TODO: add makeGroup


record GroupIso (G H : Group {ℓ}) : Type ℓ where

  constructor groupiso

  private
    module G = Group G
    module H = Group H

  field
    e : ⟨ G ⟩ ≃ ⟨ H ⟩
    isHom : (x y : ⟨ G ⟩) → equivFun e (x G.+ y) ≡ equivFun e x H.+ equivFun e y


module GroupΣ-theory {ℓ} where

  raw-group-structure : Type ℓ → Type ℓ
  raw-group-structure = SemigroupΣ-theory.raw-semigroup-structure

  raw-group-is-SNS : SNS raw-group-structure _
  raw-group-is-SNS = SemigroupΣ-theory.raw-semigroup-is-SNS

  -- The neutral element and the inverse function will be derived from the
  -- axioms, instead of being defined in the raw-group-structure in order
  -- to have that isomorphisms between groups are equivalences that preserves
  -- multiplication (so we don't have to show that they also preserve inversion
  -- and neutral element, although they will preserve them).
  group-axioms : (G : Type ℓ) → raw-group-structure G → Type ℓ
  group-axioms G _·_ =
      IsSemigroup _·_
    × (Σ[ e ∈ G ] ((x : G) → (x · e ≡ x) × (e · x ≡ x))
                × ((x : G) → Σ[ x' ∈ G ] (x · x' ≡ e) × (x' · x ≡ e)))

  group-structure : Type ℓ → Type ℓ
  group-structure = add-to-structure raw-group-structure group-axioms

  GroupΣ : Type (ℓ-suc ℓ)
  GroupΣ = TypeWithStr ℓ group-structure

  -- Iso for groups are those for monoids (but different axioms)
  group-iso : StrIso group-structure ℓ
  group-iso = add-to-iso (binaryFunIso pointed-iso) group-axioms

  open monoid-theory

  group-axioms-isProp : (X : Type ℓ)
                      → (s : raw-group-structure X)
                      → isProp (group-axioms X s)
  group-axioms-isProp X _+_ = isPropΣ (isPropIsSemigroup _) γ
    where
    γ : (h : IsSemigroup _+_) →
        isProp (Σ[ e ∈ X ] ((x : X) → (x + e ≡ x) × (e + x ≡ x))
                         × ((x : X) → Σ[ x' ∈ X ] (x + x' ≡ e) × (x' + x ≡ e)))
    γ h (e , P , _) (e' , Q , _) =
      Σ≡Prop (λ x → isPropΣ (isPropΠ λ _ → isProp× (isSetX _ _) (isSetX _ _)) (β x))
             (sym (fst (Q e)) ∙ snd (P e'))
      where
      isSetX : isSet X
      isSetX = IsSemigroup.is-set h

      β : (e : X) → ((x : X) → (x + e ≡ x) × (e + x ≡ x))
        → isProp ((x : X) → Σ[ x' ∈ X ] (x + x' ≡ e) × (x' + x ≡ e))
      β e He =
        isPropΠ λ { x (x' , _ , P) (x'' , Q , _) →
                Σ≡Prop (λ _ → isProp× (isSetX _ _) (isSetX _ _))
                       (inv-lemma ℳ x x' x'' P Q) }
        where
          ℳ : Monoid
          ℳ = makeMonoid X e _+_ isSetX (IsSemigroup.assoc h) (λ x → He x .fst) (λ x → He x .snd)

  Group→GroupΣ : Group → GroupΣ
  Group→GroupΣ (group _ _ _ -_ isGroup) =
   _ , _ , IsMonoid.isSemigroup (IsGroup.isMonoid isGroup) ,
   _ , IsMonoid.identity (IsGroup.isMonoid isGroup) ,
   λ x → (- x) , IsGroup.inverse isGroup x

  GroupΣ→Group : GroupΣ → Group
  GroupΣ→Group (_ , _ , SG , _ , H0g , w ) =
     group _ _ _ (λ x → w x .fst) (isgroup (ismonoid SG H0g) λ x → w x .snd)

  GroupIsoGroupΣ : Iso Group GroupΣ
  GroupIsoGroupΣ = iso Group→GroupΣ GroupΣ→Group (λ _ → refl) (λ _ → refl)

  group-is-SNS : SNS group-structure group-iso
  group-is-SNS = add-axioms-SNS _ group-axioms-isProp raw-group-is-SNS

  GroupΣPath : (M N : GroupΣ) → (M ≃[ group-iso ] N) ≃ (M ≡ N)
  GroupΣPath = SIP group-is-SNS

  GroupIsoΣ : (M N : Group) → Type ℓ
  GroupIsoΣ M N = Group→GroupΣ M ≃[ group-iso ] Group→GroupΣ N

  GroupIsoΣPath : {M N : Group} → Iso (GroupIso M N) (GroupIsoΣ M N)
  fun GroupIsoΣPath (groupiso e h) = (e , h)
  inv GroupIsoΣPath (e , h)        = groupiso e h
  rightInv GroupIsoΣPath _         = refl
  leftInv GroupIsoΣPath _          = refl

  GroupPath : (M N : Group) → (GroupIso M N) ≃ (M ≡ N)
  GroupPath M N =
    GroupIso M N                       ≃⟨ isoToEquiv GroupIsoΣPath ⟩
    GroupIsoΣ M N                      ≃⟨ GroupΣPath (Group→GroupΣ M) (Group→GroupΣ N) ⟩
    Group→GroupΣ M ≡ Group→GroupΣ N ≃⟨ isoToEquiv (invIso (congIso GroupIsoGroupΣ)) ⟩
    M ≡ N ■

-- Extract the characterization of equality of groups
GroupPath : (M N : Group {ℓ}) → (GroupIso M N) ≃ (M ≡ N)
GroupPath = GroupΣ-theory.GroupPath

-- This is easier to just prove directly for groups as the GroupΣ is
-- so different from the record
isPropIsGroup : {G : Type ℓ} (0g : G) (_+_ : G → G → G) (-_ : G → G)
              → isProp (IsGroup 0g _+_ -_)
isPropIsGroup 0g _+_ -_ (isgroup GM Ginv) (isgroup HM Hinv) =
  λ i → isgroup (isPropIsMonoid _ _ GM HM i) (isPropInv Ginv Hinv i)
  where
  isSetG : isSet _
  isSetG = IsSemigroup.is-set (IsMonoid.isSemigroup GM)

  isPropInv : isProp ((x : _) → ((x + (- x)) ≡ 0g) × (((- x) + x) ≡ 0g))
  isPropInv = isPropΠ λ x → isProp× (isSetG _ _) (isSetG _ _)

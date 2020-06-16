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

record IsGroup {G : Type ℓ}
               (0g : G) (_+_ : G → G → G) (-_ : G → G) : Type ℓ where

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

-- TODO: we don't need all of these arguments...
makeIsGroup : {G : Type ℓ} {0g : G} {_+_ : G → G → G} { -_ : G → G}
              (is-setG : isSet G)
              (assoc : (x y z : G) → x + (y + z) ≡ (x + y) + z)
              (rid : (x : G) → x + 0g ≡ x)
              (lid : (x : G) → 0g + x ≡ x)
              (rinv : (x : G) → x + (- x) ≡ 0g)
              (linv : (x : G) → (- x) + x ≡ 0g)
            → IsGroup 0g _+_ -_
makeIsGroup is-setG assoc rid lid rinv linv =
   isgroup (makeIsMonoid is-setG assoc rid lid) λ x → rinv x , linv x

makeGroup : {G : Type ℓ} (0g : G) (_+_ : G → G → G) (-_ : G → G)
            (is-setG : isSet G)
            (assoc : (x y z : G) → x + (y + z) ≡ (x + y) + z)
            (rid : (x : G) → x + 0g ≡ x)
            (lid : (x : G) → 0g + x ≡ x)
            (rinv : (x : G) → x + (- x) ≡ 0g)
            (linv : (x : G) → (- x) + x ≡ 0g)
          → Group
makeGroup 0g _+_ -_ is-setG assoc rid lid rinv linv =
  group _ 0g _+_ -_ (makeIsGroup is-setG assoc rid lid rinv linv)


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

  isProp-group-axioms : (G : Type ℓ)
                      → (s : raw-group-structure G)
                      → isProp (group-axioms G s)
  isProp-group-axioms G _+_ = isPropΣ (isPropIsSemigroup _) γ
    where
    γ : (h : IsSemigroup _+_) →
        isProp (Σ[ e ∈ G ] ((x : G) → (x + e ≡ x) × (e + x ≡ x))
                         × ((x : G) → Σ[ x' ∈ G ] (x + x' ≡ e) × (x' + x ≡ e)))
    γ h (e , P , _) (e' , Q , _) =
      Σ≡Prop (λ x → isPropΣ (isPropΠ λ _ → isProp× (isSetG _ _) (isSetG _ _)) (β x))
             (sym (fst (Q e)) ∙ snd (P e'))
      where
      isSetG : isSet G
      isSetG = IsSemigroup.is-set h

      β : (e : G) → ((x : G) → (x + e ≡ x) × (e + x ≡ x))
        → isProp ((x : G) → Σ[ x' ∈ G ] (x + x' ≡ e) × (x' + x ≡ e))
      β e He =
        isPropΠ λ { x (x' , _ , P) (x'' , Q , _) →
                Σ≡Prop (λ _ → isProp× (isSetG _ _) (isSetG _ _))
                       (inv-lemma ℳ x x' x'' P Q) }
        where
          ℳ : Monoid
          ℳ = makeMonoid e _+_ isSetG (IsSemigroup.assoc h) (λ x → He x .fst) (λ x → He x .snd)

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
  group-is-SNS = add-axioms-SNS _ isProp-group-axioms raw-group-is-SNS

  GroupΣPath : (G H : GroupΣ) → (G ≃[ group-iso ] H) ≃ (G ≡ H)
  GroupΣPath = SIP group-is-SNS

  GroupIsoΣ : (G H : Group) → Type ℓ
  GroupIsoΣ G H = Group→GroupΣ G ≃[ group-iso ] Group→GroupΣ H

  GroupIsoΣPath : {G H : Group} → Iso (GroupIso G H) (GroupIsoΣ G H)
  fun GroupIsoΣPath (groupiso e h) = (e , h)
  inv GroupIsoΣPath (e , h)        = groupiso e h
  rightInv GroupIsoΣPath _         = refl
  leftInv GroupIsoΣPath _          = refl

  GroupPath : (G H : Group) → (GroupIso G H) ≃ (G ≡ H)
  GroupPath G H =
    GroupIso G H                    ≃⟨ isoToEquiv GroupIsoΣPath ⟩
    GroupIsoΣ G H                   ≃⟨ GroupΣPath _ _ ⟩
    Group→GroupΣ G ≡ Group→GroupΣ H ≃⟨ isoToEquiv (invIso (congIso GroupIsoGroupΣ)) ⟩
    G ≡ H ■

-- Extract the characterization of equality of groups
GroupPath : (G H : Group {ℓ}) → (GroupIso G H) ≃ (G ≡ H)
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
  isPropInv = isPropΠ λ _ → isProp× (isSetG _ _) (isSetG _ _)

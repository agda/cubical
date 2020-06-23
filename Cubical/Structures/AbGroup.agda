{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Structures.AbGroup where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Foundations.SIP

open import Cubical.Data.Sigma

open import Cubical.Structures.Axiom
open import Cubical.Structures.Macro
open import Cubical.Structures.NAryOp
open import Cubical.Structures.Pointed
open import Cubical.Structures.Semigroup hiding (⟨_⟩)
open import Cubical.Structures.Monoid hiding (⟨_⟩)
open import Cubical.Structures.Group hiding (⟨_⟩)

open Iso

private
  variable
    ℓ : Level

record IsAbGroup {G : Type ℓ}
                 (0g : G) (_+_ : G → G → G) (-_ : G → G) : Type ℓ where

  constructor isabgroup

  field
    isGroup : IsGroup 0g _+_ -_
    comm    : (x y : G) → x + y ≡ y + x

  open IsGroup isGroup public

record AbGroup : Type (ℓ-suc ℓ) where

  constructor abgroup

  field
    Carrier   : Type ℓ
    0g        : Carrier
    _+_       : Carrier → Carrier → Carrier
    -_        : Carrier → Carrier
    isAbGroup : IsAbGroup 0g _+_ -_

  infix  8 -_
  infixl 7 _+_

  open IsAbGroup isAbGroup public

-- Extractor for the carrier type
⟨_⟩ : AbGroup → Type ℓ
⟨_⟩ = AbGroup.Carrier

makeIsAbGroup : {G : Type ℓ} {0g : G} {_+_ : G → G → G} { -_ : G → G}
              (is-setG : isSet G)
              (assoc   : (x y z : G) → x + (y + z) ≡ (x + y) + z)
              (rid     : (x : G) → x + 0g ≡ x)
              (rinv    : (x : G) → x + (- x) ≡ 0g)
              (comm    : (x y : G) → x + y ≡ y + x)
            → IsAbGroup 0g _+_ -_
makeIsAbGroup is-setG assoc rid rinv comm =
  isabgroup (makeIsGroup is-setG assoc rid (λ x → comm _ _ ∙ rid x) rinv (λ x → comm _ _ ∙ rinv x)) comm

makeAbGroup : {G : Type ℓ} (0g : G) (_+_ : G → G → G) (-_ : G → G)
            (is-setG : isSet G)
            (assoc : (x y z : G) → x + (y + z) ≡ (x + y) + z)
            (rid : (x : G) → x + 0g ≡ x)
            (rinv : (x : G) → x + (- x) ≡ 0g)
            (comm    : (x y : G) → x + y ≡ y + x)
          → AbGroup
makeAbGroup 0g _+_ -_ is-setG assoc rid rinv comm =
  abgroup _ 0g _+_ -_ (makeIsAbGroup is-setG assoc rid rinv comm)


AbGroup→Group : AbGroup {ℓ} → Group
AbGroup→Group (abgroup _ _ _ _ H) = group _ _ _ _ (IsAbGroup.isGroup H)

AbGroupIso : (G H : AbGroup) → Type ℓ
AbGroupIso G H = GroupIso (AbGroup→Group G) (AbGroup→Group H)

module AbGroupΣ-theory {ℓ} where

  open GroupΣ-theory

  abgroup-axioms : (G : Type ℓ) → raw-group-structure G → Type ℓ
  abgroup-axioms G _+_ = group-axioms G _+_ × ((x y : G) → x + y ≡ y + x)

  abgroup-structure : Type ℓ → Type ℓ
  abgroup-structure = AxiomStructure raw-group-structure abgroup-axioms

  AbGroupΣ : Type (ℓ-suc ℓ)
  AbGroupΣ = TypeWithStr ℓ abgroup-structure

  abgroup-iso : StrIso abgroup-structure ℓ
  abgroup-iso = AxiomIso (binaryFunIso PointedIso) abgroup-axioms

  isProp-abgroup-axioms : (G : Type ℓ) (s : raw-group-structure G)
                        → isProp (abgroup-axioms G s)
  isProp-abgroup-axioms G _+_ =
    isPropΣ (isProp-group-axioms G _+_)
            λ { (H , _) → isPropΠ2 λ _ _ → IsSemigroup.is-set H _ _}

  AbGroup→AbGroupΣ : AbGroup → AbGroupΣ
  AbGroup→AbGroupΣ (abgroup _ _ _ _ (isabgroup G C)) =
    _ , _ , Group→GroupΣ (group _ _ _ _ G) .snd .snd , C

  AbGroupΣ→AbGroup : AbGroupΣ → AbGroup
  AbGroupΣ→AbGroup (_ , _ , G , C) =
    abgroup _ _ _ _ (isabgroup (GroupΣ→Group (_ , _ , G) .Group.isGroup) C)

  AbGroupIsoAbGroupΣ : Iso AbGroup AbGroupΣ
  AbGroupIsoAbGroupΣ = iso AbGroup→AbGroupΣ AbGroupΣ→AbGroup (λ _ → refl) (λ _ → refl)

  abgroup-is-SNS : UnivalentStr abgroup-structure abgroup-iso
  abgroup-is-SNS = axiomUnivalentStr _ isProp-abgroup-axioms raw-group-is-SNS

  AbGroupΣPath : (G H : AbGroupΣ) → (G ≃[ abgroup-iso ] H) ≃ (G ≡ H)
  AbGroupΣPath = SIP abgroup-is-SNS

  AbGroupIsoΣ : (G H : AbGroup) → Type ℓ
  AbGroupIsoΣ G H = AbGroup→AbGroupΣ G ≃[ abgroup-iso ] AbGroup→AbGroupΣ H

  AbGroupPath : (G H : AbGroup) → (AbGroupIso G H) ≃ (G ≡ H)
  AbGroupPath G H =
    AbGroupIso G H                          ≃⟨ isoToEquiv GroupIsoΣPath ⟩
    AbGroupIsoΣ G H                         ≃⟨ AbGroupΣPath _ _ ⟩
    AbGroup→AbGroupΣ G ≡ AbGroup→AbGroupΣ H ≃⟨ isoToEquiv (invIso (congIso AbGroupIsoAbGroupΣ)) ⟩
    G ≡ H ■

-- Extract the characterization of equality of groups
AbGroupPath : (G H : AbGroup {ℓ}) → (AbGroupIso G H) ≃ (G ≡ H)
AbGroupPath = AbGroupΣ-theory.AbGroupPath

isPropIsAbGroup : {G : Type ℓ} (0g : G) (_+_ : G → G → G) (-_ : G → G)
                → isProp (IsAbGroup 0g _+_ -_)
isPropIsAbGroup 0g _+_ -_ (isabgroup GG GC) (isabgroup HG HC) =
  λ i → isabgroup (isPropIsGroup _ _ _ GG HG i) (isPropComm GC HC i)
  where
  isSetG : isSet _
  isSetG = GG .IsGroup.isMonoid .IsMonoid.isSemigroup .IsSemigroup.is-set

  isPropComm : isProp ((x y : _) → x + y ≡ y + x)
  isPropComm = isPropΠ2 λ _ _ → isSetG _ _

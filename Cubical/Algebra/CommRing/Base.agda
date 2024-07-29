{-# OPTIONS --safe #-}
module Cubical.Algebra.CommRing.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.SIP

open import Cubical.Data.Sigma

open import Cubical.Displayed.Base
open import Cubical.Displayed.Auto
open import Cubical.Displayed.Record
open import Cubical.Displayed.Universe

open import Cubical.Algebra.Ring.Base
open import Cubical.Algebra.AbGroup

open import Cubical.Reflection.RecordEquiv

open Iso

private
  variable
    ℓ ℓ' : Level

record IsCommRing {R : Type ℓ}
                  (0r 1r : R) (_+_ _·_ : R → R → R) (-_ : R → R) : Type ℓ where

  constructor iscommring

  field
    isRing : IsRing 0r 1r _+_ _·_ -_
    ·Comm : (x y : R) → x · y ≡ y · x

  open IsRing isRing public

unquoteDecl IsCommRingIsoΣ = declareRecordIsoΣ IsCommRingIsoΣ (quote IsCommRing)

record CommRingStr (A : Type ℓ) : Type (ℓ-suc ℓ) where

  constructor commringstr

  field
    0r         : A
    1r         : A
    _+_        : A → A → A
    _·_        : A → A → A
    -_         : A → A
    isCommRing : IsCommRing 0r 1r _+_ _·_ -_

  infix  8 -_
  infixl 7 _·_
  infixl 6 _+_

  open IsCommRing isCommRing public

CommRing : ∀ ℓ → Type (ℓ-suc ℓ)
CommRing ℓ = TypeWithStr ℓ CommRingStr


makeIsCommRing : {R : Type ℓ} {0r 1r : R} {_+_ _·_ : R → R → R} { -_ : R → R}
                 (is-setR : isSet R)
                 (+Assoc : (x y z : R) → x + (y + z) ≡ (x + y) + z)
                 (+IdR : (x : R) → x + 0r ≡ x)
                 (+InvR : (x : R) → x + (- x) ≡ 0r)
                 (+Comm : (x y : R) → x + y ≡ y + x)
                 (·Assoc : (x y z : R) → x · (y · z) ≡ (x · y) · z)
                 (·IdR : (x : R) → x · 1r ≡ x)
                 (·DistR+ : (x y z : R) → x · (y + z) ≡ (x · y) + (x · z))
                 (·Comm : (x y : R) → x · y ≡ y · x)
               → IsCommRing 0r 1r _+_ _·_ -_
makeIsCommRing {_+_ = _+_} is-setR +Assoc +IdR +InvR +Comm ·Assoc ·IdR ·DistR+ ·Comm =
  iscommring (makeIsRing is-setR +Assoc +IdR +InvR +Comm ·Assoc ·IdR
                         (λ x → ·Comm _ _ ∙ ·IdR x) ·DistR+
                         (λ x y z → ·Comm _ _ ∙∙ ·DistR+ z x y ∙∙ λ i → (·Comm z x i) + (·Comm z y i))) ·Comm

makeCommRing : {R : Type ℓ} (0r 1r : R) (_+_ _·_ : R → R → R) (-_ : R → R)
               (is-setR : isSet R)
               (+Assoc : (x y z : R) → x + (y + z) ≡ (x + y) + z)
               (+IdR : (x : R) → x + 0r ≡ x)
               (+InvR : (x : R) → x + (- x) ≡ 0r)
               (+Comm : (x y : R) → x + y ≡ y + x)
               (·Assoc : (x y z : R) → x · (y · z) ≡ (x · y) · z)
               (·IdR : (x : R) → x · 1r ≡ x)
               (·DistR+ : (x y z : R) → x · (y + z) ≡ (x · y) + (x · z))
               (·Comm : (x y : R) → x · y ≡ y · x)
             → CommRing ℓ
makeCommRing 0r 1r _+_ _·_ -_ is-setR +Assoc +IdR +InvR +Comm ·Assoc ·IdR ·DistR+ ·Comm =
  _ , commringstr _ _ _ _ _ (makeIsCommRing is-setR +Assoc +IdR +InvR +Comm ·Assoc ·IdR ·DistR+ ·Comm)

CommRingStr→RingStr : {A : Type ℓ} → CommRingStr A → RingStr A
CommRingStr→RingStr (commringstr _ _ _ _ _ H) = ringstr _ _ _ _ _ (IsCommRing.isRing H)

CommRing→Ring : CommRing ℓ → Ring ℓ
CommRing→Ring (_ , commringstr _ _ _ _ _ H) = _ , ringstr _ _ _ _ _ (IsCommRing.isRing H)

CommRing→AbGroup : CommRing ℓ → AbGroup ℓ
CommRing→AbGroup R = Ring→AbGroup (CommRing→Ring R)

Ring→CommRing : (R : Ring ℓ) → ((x y : (fst R)) → (RingStr._·_ (snd R) x y ≡ RingStr._·_ (snd R) y x)) → CommRing ℓ
fst (Ring→CommRing R p) = fst R
CommRingStr.0r (snd (Ring→CommRing R p)) = RingStr.0r (snd R)
CommRingStr.1r (snd (Ring→CommRing R p)) = RingStr.1r (snd R)
CommRingStr._+_ (snd (Ring→CommRing R p)) = RingStr._+_ (snd R)
CommRingStr._·_ (snd (Ring→CommRing R p)) = RingStr._·_ (snd R)
CommRingStr.- snd (Ring→CommRing R p) = RingStr.-_ (snd R)
IsCommRing.isRing (CommRingStr.isCommRing (snd (Ring→CommRing R p))) = RingStr.isRing (snd R)
IsCommRing.·Comm (CommRingStr.isCommRing (snd (Ring→CommRing R p))) = p

record IsCommRingHom {A : Type ℓ} {B : Type ℓ'} (R : CommRingStr A) (f : A → B) (S : CommRingStr B)
  : Type (ℓ-max ℓ ℓ')
  where

  -- Shorter qualified names
  private
    module R = CommRingStr R
    module S = CommRingStr S

  field
    pres0 : f R.0r ≡ S.0r
    pres1 : f R.1r ≡ S.1r
    pres+ : (x y : A) → f (x R.+ y) ≡ f x S.+ f y
    pres· : (x y : A) → f (x R.· y) ≡ f x S.· f y
    pres- : (x : A) → f (R.- x) ≡ S.- (f x)

CommRingHom : (R : CommRing ℓ) (S : CommRing ℓ') → Type (ℓ-max ℓ ℓ')
CommRingHom R S = RingHom (CommRing→Ring R) (CommRing→Ring S)

IsCommRingEquiv : {A : Type ℓ} {B : Type ℓ'}
  (R : CommRingStr A) (e : A ≃ B) (S : CommRingStr B) → Type (ℓ-max ℓ ℓ')
IsCommRingEquiv R e S = IsRingHom (CommRingStr→RingStr R) (e .fst) (CommRingStr→RingStr S)

CommRingEquiv : (R : CommRing ℓ) (S : CommRing ℓ') → Type (ℓ-max ℓ ℓ')
CommRingEquiv R S = Σ[ e ∈ (R .fst ≃ S .fst) ] IsCommRingEquiv (R .snd) e (S .snd)

CommRingEquiv→CommRingHom : {A : CommRing ℓ} {B : CommRing ℓ'} → CommRingEquiv A B → CommRingHom A B
CommRingEquiv→CommRingHom (e , eIsHom) = e .fst , eIsHom

isPropIsCommRing : {R : Type ℓ} (0r 1r : R) (_+_ _·_ : R → R → R) (-_ : R → R)
             → isProp (IsCommRing 0r 1r _+_ _·_ -_)
isPropIsCommRing 0r 1r _+_ _·_ -_ =
  isOfHLevelRetractFromIso 1 IsCommRingIsoΣ
  (isPropΣ (isPropIsRing 0r 1r _+_ _·_ (-_))
  (λ ring → isPropΠ2 (λ _ _ → is-set ring _ _)))
  where
  open IsRing

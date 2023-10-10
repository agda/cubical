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

𝒮ᴰ-CommRing : DUARel (𝒮-Univ ℓ) CommRingStr ℓ
𝒮ᴰ-CommRing =
  𝒮ᴰ-Record (𝒮-Univ _) IsCommRingEquiv
    (fields:
      data[ 0r ∣ null ∣ pres0 ]
      data[ 1r ∣ null ∣ pres1 ]
      data[ _+_ ∣ bin ∣ pres+ ]
      data[ _·_ ∣ bin ∣ pres· ]
      data[ -_ ∣ autoDUARel _ _ ∣ pres- ]
      prop[ isCommRing ∣ (λ _ _ → isPropIsCommRing _ _ _ _ _) ])
 where
  open CommRingStr
  open IsRingHom

  -- faster with some sharing
  null = autoDUARel (𝒮-Univ _) (λ A → A)
  bin = autoDUARel (𝒮-Univ _) (λ A → A → A → A)

CommRingPath : (R S : CommRing ℓ) → CommRingEquiv R S ≃ (R ≡ S)
CommRingPath = ∫ 𝒮ᴰ-CommRing .UARel.ua

uaCommRing : {A B : CommRing ℓ} → CommRingEquiv A B → A ≡ B
uaCommRing {A = A} {B = B} = equivFun (CommRingPath A B)

CommRingIso : (R : CommRing ℓ) (S : CommRing ℓ') → Type (ℓ-max ℓ ℓ')
CommRingIso R S = Σ[ e ∈ Iso (R .fst) (S .fst) ]
                     IsRingHom (CommRingStr→RingStr (R .snd)) (e .fun) (CommRingStr→RingStr (S .snd))

CommRingEquivIsoCommRingIso : (R : CommRing ℓ) (S : CommRing ℓ') → Iso (CommRingEquiv R S) (CommRingIso R S)
fst (fun (CommRingEquivIsoCommRingIso R S) e) = equivToIso (e .fst)
snd (fun (CommRingEquivIsoCommRingIso R S) e) = e .snd
fst (inv (CommRingEquivIsoCommRingIso R S) e) = isoToEquiv (e .fst)
snd (inv (CommRingEquivIsoCommRingIso R S) e) = e .snd
rightInv (CommRingEquivIsoCommRingIso R S) (e , he) =
  Σ≡Prop (λ e → isPropIsRingHom (snd (CommRing→Ring R)) (e .fun) (snd (CommRing→Ring S)))
         rem
  where
  rem : equivToIso (isoToEquiv e) ≡ e
  fun (rem i) x = fun e x
  inv (rem i) x = inv e x
  rightInv (rem i) b j = CommRingStr.is-set (snd S) (fun e (inv e b)) b (rightInv e b) (rightInv e b) i j
  leftInv (rem i) a j = CommRingStr.is-set (snd R) (inv e (fun e a)) a (retEq (isoToEquiv e) a) (leftInv e a) i j
leftInv (CommRingEquivIsoCommRingIso R S) e =
  Σ≡Prop (λ e → isPropIsRingHom (snd (CommRing→Ring R)) (e .fst) (snd (CommRing→Ring S)))
         (equivEq refl)

isGroupoidCommRing : isGroupoid (CommRing ℓ)
isGroupoidCommRing _ _ = isOfHLevelRespectEquiv 2 (CommRingPath _ _) (isSetRingEquiv _ _)

open CommRingStr
open IsRingHom

-- TODO: Induced structure results are temporarily inconvenient while we transition between algebra
-- representations
module _ (R : CommRing ℓ) {A : Type ℓ}
  (0a 1a : A)
  (add mul : A → A → A)
  (inv : A → A)
  (e : ⟨ R ⟩ ≃ A)
  (p0 : e .fst (R .snd .0r) ≡ 0a)
  (p1 : e .fst (R .snd .1r) ≡ 1a)
  (p+ : ∀ x y → e .fst (R .snd ._+_ x y) ≡ add (e .fst x) (e .fst y))
  (p· : ∀ x y → e .fst (R .snd ._·_ x y) ≡ mul (e .fst x) (e .fst y))
  (pinv : ∀ x → e .fst (R .snd .-_ x) ≡ inv (e .fst x))
  where

  private
    module R = CommRingStr (R .snd)

    BaseΣ : Type (ℓ-suc ℓ)
    BaseΣ = Σ[ B ∈ Type ℓ ] B × B × (B → B → B) × (B → B → B) × (B → B)

    FamilyΣ : BaseΣ → Type ℓ
    FamilyΣ (B , u0 , u1 , a , m , i) = IsCommRing u0 u1 a m i

    inducedΣ : FamilyΣ (A , 0a , 1a , add , mul , inv)
    inducedΣ =
      subst FamilyΣ
        (UARel.≅→≡ (autoUARel BaseΣ) (e , p0 , p1 , p+ , p· , pinv))
        R.isCommRing

  InducedCommRing : CommRing ℓ
  InducedCommRing .fst = A
  0r (InducedCommRing .snd) = 0a
  1r (InducedCommRing .snd) = 1a
  _+_ (InducedCommRing .snd) = add
  _·_ (InducedCommRing .snd) = mul
  - InducedCommRing .snd = inv
  isCommRing (InducedCommRing .snd) = inducedΣ

  InducedCommRingEquiv : CommRingEquiv R InducedCommRing
  fst InducedCommRingEquiv = e
  pres0 (snd InducedCommRingEquiv) = p0
  pres1 (snd InducedCommRingEquiv) = p1
  pres+ (snd InducedCommRingEquiv) = p+
  pres· (snd InducedCommRingEquiv) = p·
  pres- (snd InducedCommRingEquiv) = pinv

  InducedCommRingPath : R ≡ InducedCommRing
  InducedCommRingPath = CommRingPath _ _ .fst InducedCommRingEquiv

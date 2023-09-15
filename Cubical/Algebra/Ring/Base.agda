{-# OPTIONS --safe #-}
module Cubical.Algebra.Ring.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.SIP

open import Cubical.Data.Sigma

open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.AbGroup

open import Cubical.Displayed.Base
open import Cubical.Displayed.Auto
open import Cubical.Displayed.Record
open import Cubical.Displayed.Universe

open import Cubical.Reflection.RecordEquiv


open Iso

private
  variable
    ℓ ℓ' ℓ'' : Level

record IsRing {R : Type ℓ}
              (0r 1r : R) (_+_ _·_ : R → R → R) (-_ : R → R) : Type ℓ where

  constructor isring

  field
    +IsAbGroup : IsAbGroup 0r _+_ -_
    ·IsMonoid  : IsMonoid 1r _·_
    ·DistR+ : (x y z : R) → x · (y + z) ≡ (x · y) + (x · z)
    ·DistL+ : (x y z : R) → (x + y) · z ≡ (x · z) + (y · z)
    -- This is in the Agda stdlib, but it's redundant
    -- zero             : (x : R) → (x · 0r ≡ 0r) × (0r · x ≡ 0r)

  open IsAbGroup +IsAbGroup public
    renaming
      ( isSemigroup  to +IsSemigroup
      ; isMonoid     to +IsMonoid
      ; isGroup      to +IsGroup )

  open IsMonoid ·IsMonoid public
    renaming
      ( isSemigroup to ·IsSemigroup )
    hiding
      ( is-set ) -- We only want to export one proof of this


unquoteDecl IsRingIsoΣ = declareRecordIsoΣ IsRingIsoΣ (quote IsRing)


record RingStr (A : Type ℓ) : Type (ℓ-suc ℓ) where

  constructor ringstr

  field
    0r      : A
    1r      : A
    _+_     : A → A → A
    _·_     : A → A → A
    -_      : A → A
    isRing  : IsRing 0r 1r _+_ _·_ -_

  infix  8 -_
  infixl 7 _·_
  infixl 6 _+_

  open IsRing isRing public

Ring : ∀ ℓ → Type (ℓ-suc ℓ)
Ring ℓ = TypeWithStr ℓ RingStr

module _ {R : Type ℓ} {0r 1r : R} {_+_ _·_ : R → R → R} { -_ : R → R}
               (is-setR : isSet R)
               (+Assoc : (x y z : R) → x + (y + z) ≡ (x + y) + z)
               (+IdR : (x : R) → x + 0r ≡ x)
               (+InvR : (x : R) → x + (- x) ≡ 0r)
               (+Comm : (x y : R) → x + y ≡ y + x)
               (·Assoc : (x y z : R) → x · (y · z) ≡ (x · y) · z)
               (·IdR : (x : R) → x · 1r ≡ x)
               (·IdL : (x : R) → 1r · x ≡ x)
               (·DistR+ : (x y z : R) → x · (y + z) ≡ (x · y) + (x · z))
               (·DistL+ : (x y z : R) → (x + y) · z ≡ (x · z) + (y · z))
  where

  makeIsRing : IsRing 0r 1r _+_ _·_ -_
  makeIsRing .IsRing.+IsAbGroup = makeIsAbGroup is-setR +Assoc +IdR +InvR +Comm
  makeIsRing .IsRing.·IsMonoid = makeIsMonoid is-setR ·Assoc ·IdR ·IdL
  makeIsRing .IsRing.·DistR+ = ·DistR+
  makeIsRing .IsRing.·DistL+ = ·DistL+

module _ {R : Type ℓ} (0r 1r : R) (_+_ _·_ : R → R → R) (-_ : R → R)
               (is-setR : isSet R)
               (+Assoc : (x y z : R) → x + (y + z) ≡ (x + y) + z)
               (+IdR : (x : R) → x + 0r ≡ x)
               (+InvR : (x : R) → x + (- x) ≡ 0r)
               (+Comm : (x y : R) → x + y ≡ y + x)
               (·Assoc : (x y z : R) → x · (y · z) ≡ (x · y) · z)
               (·IdR : (x : R) → x · 1r ≡ x)
               (·IdL : (x : R) → 1r · x ≡ x)
               (·DistR+ : (x y z : R) → x · (y + z) ≡ (x · y) + (x · z))
               (·DistL+ : (x y z : R) → (x + y) · z ≡ (x · z) + (y · z))
  where

  makeRing : Ring ℓ
  makeRing .fst = R
  makeRing .snd .RingStr.0r = 0r
  makeRing .snd .RingStr.1r = 1r
  makeRing .snd .RingStr._+_ = _+_
  makeRing .snd .RingStr._·_ = _·_
  makeRing .snd .RingStr.-_ = -_
  makeRing .snd .RingStr.isRing =
    makeIsRing is-setR +Assoc +IdR +InvR +Comm
                       ·Assoc ·IdR ·IdL ·DistR+ ·DistL+

record IsRingHom {A : Type ℓ} {B : Type ℓ'} (R : RingStr A) (f : A → B) (S : RingStr B)
  : Type (ℓ-max ℓ ℓ')
  where

  -- Shorter qualified names
  private
    module R = RingStr R
    module S = RingStr S

  field
    pres0 : f R.0r ≡ S.0r
    pres1 : f R.1r ≡ S.1r
    pres+ : (x y : A) → f (x R.+ y) ≡ f x S.+ f y
    pres· : (x y : A) → f (x R.· y) ≡ f x S.· f y
    pres- : (x : A) → f (R.- x) ≡ S.- (f x)

unquoteDecl IsRingHomIsoΣ = declareRecordIsoΣ IsRingHomIsoΣ (quote IsRingHom)

RingHom : (R : Ring ℓ) (S : Ring ℓ') → Type (ℓ-max ℓ ℓ')
RingHom R S = Σ[ f ∈ (⟨ R ⟩ → ⟨ S ⟩) ] IsRingHom (R .snd) f (S .snd)

IsRingEquiv : {A : Type ℓ} {B : Type ℓ'} (M : RingStr A) (e : A ≃ B) (N : RingStr B)
  → Type (ℓ-max ℓ ℓ')
IsRingEquiv M e N = IsRingHom M (e .fst) N

RingEquiv : (R : Ring ℓ) (S : Ring ℓ') → Type (ℓ-max ℓ ℓ')
RingEquiv R S = Σ[ e ∈ (⟨ R ⟩ ≃ ⟨ S ⟩) ] IsRingEquiv (R .snd) e (S .snd)

_$r_ : {R : Ring ℓ} {S : Ring ℓ'} → (φ : RingHom R S) → (x : ⟨ R ⟩) → ⟨ S ⟩
φ $r x = φ .fst x

RingEquiv→RingHom : {A B : Ring ℓ} → RingEquiv A B → RingHom A B
RingEquiv→RingHom (e , eIsHom) = e .fst , eIsHom

RingHomIsEquiv→RingEquiv : {A B : Ring ℓ} (f : RingHom A B)
                         → isEquiv (fst f) → RingEquiv A B
fst (fst (RingHomIsEquiv→RingEquiv f fIsEquiv)) = fst f
snd (fst (RingHomIsEquiv→RingEquiv f fIsEquiv)) = fIsEquiv
snd (RingHomIsEquiv→RingEquiv f fIsEquiv) = snd f

isPropIsRing : {R : Type ℓ} (0r 1r : R) (_+_ _·_ : R → R → R) (-_ : R → R)
             → isProp (IsRing 0r 1r _+_ _·_ -_)
isPropIsRing 0r 1r _+_ _·_ -_ =
  isOfHLevelRetractFromIso 1 IsRingIsoΣ
    (isPropΣ (isPropIsAbGroup 0r _+_ (-_)) λ abgrp →
     isProp× (isPropIsMonoid 1r _·_)
             (isProp× (isPropΠ3 λ _ _ _ → abgrp .is-set _ _)
                      (isPropΠ3 λ _ _ _ → abgrp .is-set _ _)))
  where
  open IsAbGroup

isPropIsRingHom : {A : Type ℓ} {B : Type ℓ'} (R : RingStr A) (f : A → B) (S : RingStr B)
  → isProp (IsRingHom R f S)
isPropIsRingHom R f S = isOfHLevelRetractFromIso 1 IsRingHomIsoΣ
                        (isProp×4 (is-set _ _)
                                  (is-set _ _)
                                  (isPropΠ2 λ _ _ → is-set _ _)
                                  (isPropΠ2 λ _ _ → is-set _ _)
                                  (isPropΠ λ _ → is-set _ _))
  where
  open RingStr S using (is-set)

isSetRingHom : (R : Ring ℓ) (S : Ring ℓ') → isSet (RingHom R S)
isSetRingHom R S = isSetΣSndProp (isSetΠ λ _ → is-set) (λ f → isPropIsRingHom (snd R) f (snd S))
  where
  open RingStr (str S) using (is-set)

isSetRingEquiv : (A : Ring ℓ) (B : Ring ℓ') → isSet (RingEquiv A B)
isSetRingEquiv A B = isSetΣSndProp (isOfHLevel≃ 2 A.is-set B.is-set)
                                   (λ e → isPropIsRingHom (snd A) (fst e) (snd B))
  where
  module A = RingStr (str A)
  module B = RingStr (str B)

RingHomPathP : (R : Ring ℓ) (S T : Ring ℓ') (p : S ≡ T) (φ : RingHom R S) (ψ : RingHom R T)
             → PathP (λ i → R .fst → p i .fst) (φ .fst) (ψ .fst)
             → PathP (λ i → RingHom R (p i)) φ ψ
RingHomPathP R S T p φ ψ q = ΣPathP (q , isProp→PathP (λ _ → isPropIsRingHom _ _ _) _ _)

RingHom≡ : {R : Ring ℓ} {S : Ring ℓ'} {φ ψ : RingHom R S} → fst φ ≡ fst ψ → φ ≡ ψ
RingHom≡ = Σ≡Prop λ f → isPropIsRingHom _ f _

𝒮ᴰ-Ring : DUARel (𝒮-Univ ℓ) RingStr ℓ
𝒮ᴰ-Ring =
  𝒮ᴰ-Record (𝒮-Univ _) IsRingEquiv
    (fields:
      data[ 0r ∣ null ∣ pres0 ]
      data[ 1r ∣ null ∣ pres1 ]
      data[ _+_ ∣ bin ∣ pres+ ]
      data[ _·_ ∣ bin ∣ pres· ]
      data[ -_ ∣ un ∣ pres- ]
      prop[ isRing ∣ (λ _ _ → isPropIsRing _ _ _ _ _) ])
 where
  open RingStr
  open IsRingHom

  -- faster with some sharing
  null = autoDUARel (𝒮-Univ _) (λ A → A)
  un = autoDUARel (𝒮-Univ _) (λ A → A → A)
  bin = autoDUARel (𝒮-Univ _) (λ A → A → A → A)

RingPath : (R S : Ring ℓ) → RingEquiv R S ≃ (R ≡ S)
RingPath = ∫ 𝒮ᴰ-Ring .UARel.ua

uaRing : {A B : Ring ℓ} → RingEquiv A B → A ≡ B
uaRing {A = A} {B = B} = equivFun (RingPath A B)

isGroupoidRing : isGroupoid (Ring ℓ)
isGroupoidRing _ _ = isOfHLevelRespectEquiv 2 (RingPath _ _) (isSetRingEquiv _ _)

open RingStr
open IsRingHom

-- TODO: Induced structure results are temporarily inconvenient while we transition between algebra
-- representations
module _ (R : Ring ℓ) {A : Type ℓ}
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
    module R = RingStr (R .snd)

    BaseΣ : Type (ℓ-suc ℓ)
    BaseΣ = Σ[ B ∈ Type ℓ ] B × B × (B → B → B) × (B → B → B) × (B → B)

    FamilyΣ : BaseΣ → Type ℓ
    FamilyΣ (B , u0 , u1 , a , m , i) = IsRing u0 u1 a m i

    inducedΣ : FamilyΣ (A , 0a , 1a , add , mul , inv)
    inducedΣ =
      subst FamilyΣ
        (UARel.≅→≡ (autoUARel BaseΣ) (e , p0 , p1 , p+ , p· , pinv))
        R.isRing

  InducedRing : Ring ℓ
  InducedRing .fst = A
  0r (InducedRing .snd) = 0a
  1r (InducedRing .snd) = 1a
  _+_ (InducedRing .snd) = add
  _·_ (InducedRing .snd) = mul
  - InducedRing .snd = inv
  isRing (InducedRing .snd) = inducedΣ

  InducedRingEquiv : RingEquiv R InducedRing
  fst InducedRingEquiv = e
  pres0 (snd InducedRingEquiv) = p0
  pres1 (snd InducedRingEquiv) = p1
  pres+ (snd InducedRingEquiv) = p+
  pres· (snd InducedRingEquiv) = p·
  pres- (snd InducedRingEquiv) = pinv

  InducedRingPath : R ≡ InducedRing
  InducedRingPath = RingPath _ _ .fst InducedRingEquiv




-- Rings have an abelian group and a monoid

module _ ((A , (ringstr 0r 1r _+_ _·_ -_ R)) : Ring ℓ) where
  Ring→AbGroup : AbGroup ℓ
  Ring→AbGroup .fst = A
  Ring→AbGroup .snd .AbGroupStr.0g = 0r
  Ring→AbGroup .snd .AbGroupStr._+_ = _+_
  Ring→AbGroup .snd .AbGroupStr.-_ = -_
  Ring→AbGroup .snd .AbGroupStr.isAbGroup = IsRing.+IsAbGroup R

  Ring→MultMonoid : Monoid ℓ
  Ring→MultMonoid = monoid A 1r _·_ (IsRing.·IsMonoid R)

Ring→Group : Ring ℓ → Group ℓ
Ring→Group = AbGroup→Group ∘ Ring→AbGroup

Ring→AddMonoid : Ring ℓ → Monoid ℓ
Ring→AddMonoid = Group→Monoid ∘ Ring→Group

-- Smart constructor for ring homomorphisms
-- that infers the other equations from pres1, pres+, and pres·

module _ {R : Ring ℓ} {S : Ring ℓ'} {f : ⟨ R ⟩ → ⟨ S ⟩} where

  private
    module R = RingStr (R .snd)
    module S = RingStr (S .snd)

  module _
    (p1 : f R.1r ≡ S.1r)
    (p+ : (x y : ⟨ R ⟩) → f (x R.+ y) ≡ f x S.+ f y)
    (p· : (x y : ⟨ R ⟩) → f (x R.· y) ≡ f x S.· f y)
    where

    open IsRingHom
    private
      isGHom : IsGroupHom (Ring→Group R .snd) f (Ring→Group S .snd)
      isGHom = makeIsGroupHom p+

    makeIsRingHom : IsRingHom (R .snd) f (S .snd)
    makeIsRingHom .pres0 = isGHom .IsGroupHom.pres1
    makeIsRingHom .pres1 = p1
    makeIsRingHom .pres+ = p+
    makeIsRingHom .pres· = p·
    makeIsRingHom .pres- = isGHom .IsGroupHom.presinv

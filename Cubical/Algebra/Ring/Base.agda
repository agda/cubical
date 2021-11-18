{-# OPTIONS --safe #-}
module Cubical.Algebra.Ring.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Foundations.SIP

open import Cubical.Data.Sigma

open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Group
open import Cubical.Algebra.AbGroup

open import Cubical.Displayed.Base
open import Cubical.Displayed.Auto
open import Cubical.Displayed.Record
open import Cubical.Displayed.Universe

open import Cubical.Reflection.RecordEquiv

open Iso

private
  variable
    ℓ ℓ' : Level

record IsRing {R : Type ℓ}
              (0r 1r : R) (_+_ _·_ : R → R → R) (-_ : R → R) : Type ℓ where

  constructor isring

  field
    +IsAbGroup : IsAbGroup 0r _+_ -_
    ·IsMonoid  : IsMonoid 1r _·_
    dist        : (x y z : R) → (x · (y + z) ≡ (x · y) + (x · z))
                              × ((x + y) · z ≡ (x · z) + (y · z))
    -- This is in the Agda stdlib, but it's redundant
    -- zero             : (x : R) → (x · 0r ≡ 0r) × (0r · x ≡ 0r)

  open IsAbGroup +IsAbGroup public
    renaming
      ( assoc       to +Assoc
      ; identity    to +Identity
      ; lid         to +Lid
      ; rid         to +Rid
      ; inverse     to +Inv
      ; invl        to +Linv
      ; invr        to +Rinv
      ; comm        to +Comm
      ; isSemigroup to +IsSemigroup
      ; isMonoid    to +IsMonoid
      ; isGroup     to +IsGroup )

  open IsMonoid ·IsMonoid public
    renaming
      ( assoc       to ·Assoc
      ; identity    to ·Identity
      ; lid         to ·Lid
      ; rid         to ·Rid
      ; isSemigroup to ·IsSemigroup )
    hiding
      ( is-set ) -- We only want to export one proof of this

  ·Rdist+ : (x y z : R) → x · (y + z) ≡ (x · y) + (x · z)
  ·Rdist+ x y z = dist x y z .fst

  ·Ldist+ : (x y z : R) → (x + y) · z ≡ (x · z) + (y · z)
  ·Ldist+ x y z = dist x y z .snd

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

isSetRing : (R : Ring ℓ) → isSet ⟨ R ⟩
isSetRing R = R .snd .RingStr.isRing .IsRing.·IsMonoid .IsMonoid.isSemigroup .IsSemigroup.is-set

makeIsRing : {R : Type ℓ} {0r 1r : R} {_+_ _·_ : R → R → R} { -_ : R → R}
             (is-setR : isSet R)
             (+-assoc : (x y z : R) → x + (y + z) ≡ (x + y) + z)
             (+-rid : (x : R) → x + 0r ≡ x)
             (+-rinv : (x : R) → x + (- x) ≡ 0r)
             (+-comm : (x y : R) → x + y ≡ y + x)
             (r+-assoc : (x y z : R) → x · (y · z) ≡ (x · y) · z)
             (·-rid : (x : R) → x · 1r ≡ x)
             (·-lid : (x : R) → 1r · x ≡ x)
             (·-rdist-+ : (x y z : R) → x · (y + z) ≡ (x · y) + (x · z))
             (·-ldist-+ : (x y z : R) → (x + y) · z ≡ (x · z) + (y · z))
           → IsRing 0r 1r _+_ _·_ -_
makeIsRing is-setR assoc +-rid +-rinv +-comm ·-assoc ·-rid ·-lid ·-rdist-+ ·-ldist-+ =
  isring (makeIsAbGroup is-setR assoc +-rid +-rinv +-comm)
         (makeIsMonoid is-setR ·-assoc ·-rid ·-lid)
         λ x y z → ·-rdist-+ x y z , ·-ldist-+ x y z

makeRing : {R : Type ℓ} (0r 1r : R) (_+_ _·_ : R → R → R) (-_ : R → R)
           (is-setR : isSet R)
           (+-assoc : (x y z : R) → x + (y + z) ≡ (x + y) + z)
           (+-rid : (x : R) → x + 0r ≡ x)
           (+-rinv : (x : R) → x + (- x) ≡ 0r)
           (+-comm : (x y : R) → x + y ≡ y + x)
           (+-assoc : (x y z : R) → x · (y · z) ≡ (x · y) · z)
           (·-rid : (x : R) → x · 1r ≡ x)
           (·-lid : (x : R) → 1r · x ≡ x)
           (·-rdist-+ : (x y z : R) → x · (y + z) ≡ (x · y) + (x · z))
           (·-ldist-+ : (x y z : R) → (x + y) · z ≡ (x · z) + (y · z))
         → Ring ℓ
makeRing 0r 1r _+_ _·_ -_ is-setR assoc +-rid +-rinv +-comm ·-assoc ·-rid ·-lid ·-rdist-+ ·-ldist-+ =
  _ , ringstr 0r 1r _+_ _·_ -_
       (makeIsRing is-setR assoc +-rid +-rinv +-comm
                   ·-assoc ·-rid ·-lid ·-rdist-+ ·-ldist-+ )

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

_$_ : {R S : Ring ℓ} → (φ : RingHom R S) → (x : ⟨ R ⟩) → ⟨ S ⟩
φ $ x = φ .fst x

RingEquiv→RingHom : {A B : Ring ℓ} → RingEquiv A B → RingHom A B
RingEquiv→RingHom (e , eIsHom) = e .fst , eIsHom

isPropIsRing : {R : Type ℓ} (0r 1r : R) (_+_ _·_ : R → R → R) (-_ : R → R)
             → isProp (IsRing 0r 1r _+_ _·_ -_)
isPropIsRing 0r 1r _+_ _·_ -_ (isring RG RM RD) (isring SG SM SD) =
  λ i → isring (isPropIsAbGroup _ _ _ RG SG i)
               (isPropIsMonoid _ _ RM SM i)
               (isPropDistr RD SD i)
  where
  isSetR : isSet _
  isSetR = RM .IsMonoid.isSemigroup .IsSemigroup.is-set

  isPropDistr : isProp ((x y z : _) → ((x · (y + z)) ≡ ((x · y) + (x · z)))
                                    × (((x + y) · z) ≡ ((x · z) + (y · z))))
  isPropDistr = isPropΠ3 λ _ _ _ → isProp× (isSetR _ _) (isSetR _ _)

isPropIsRingHom : {A : Type ℓ} {B : Type ℓ'} (R : RingStr A) (f : A → B) (S : RingStr B)
  → isProp (IsRingHom R f S)
isPropIsRingHom R f S = isOfHLevelRetractFromIso 1 IsRingHomIsoΣ
                        (isProp×4 (isSetRing (_ , S) _ _)
                                  (isSetRing (_ , S) _ _)
                                  (isPropΠ2 λ _ _ → isSetRing (_ , S) _ _)
                                  (isPropΠ2 λ _ _ → isSetRing (_ , S) _ _)
                                  (isPropΠ λ _ → isSetRing (_ , S) _ _))

RingHomPathP : (R S T : Ring ℓ) (p : S ≡ T) (φ : RingHom R S) (ψ : RingHom R T)
             → PathP (λ i → R .fst → p i .fst) (φ .fst) (ψ .fst)
             → PathP (λ i → RingHom R (p i)) φ ψ
RingHomPathP R S T p φ ψ q = ΣPathP (q , isProp→PathP (λ _ → isPropIsRingHom _ _ _) _ _)

RingHom≡ : {R S : Ring ℓ} {φ ψ : RingHom R S} → fst φ ≡ fst ψ → φ ≡ ψ
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

-- Rings have an abelian group and a monoid

Ring→AbGroup : Ring ℓ → AbGroup ℓ
Ring→AbGroup (A , ringstr _ _ _ _ _ R) = A , abgroupstr _ _ _ (IsRing.+IsAbGroup R)

Ring→Group : Ring ℓ → Group ℓ
Ring→Group = AbGroup→Group ∘ Ring→AbGroup

Ring→AddMonoid : Ring ℓ → Monoid ℓ
Ring→AddMonoid = Group→Monoid ∘ Ring→Group

Ring→MultMonoid : Ring ℓ → Monoid ℓ
Ring→MultMonoid (A , ringstr _ _ _ _ _ R) = monoid _ _ _ (IsRing.·IsMonoid R)

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

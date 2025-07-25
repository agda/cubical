module Cubical.Algebra.CommRing.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function using (_$_)
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
CommRingStr→RingStr cringStr =
  record
    { 0r = _ ; 1r = _ ; _+_ = _ ; _·_ = _ ; -_ = _ ;
      isRing = IsCommRing.isRing (CommRingStr.isCommRing cringStr) }

CommRing→Ring : CommRing ℓ → Ring ℓ
fst (CommRing→Ring CRing) = fst CRing
snd (CommRing→Ring CRing) = record
                             { 0r =  _
                             ; 1r =  _
                             ; _+_ = _
                             ; _·_ = _
                             ; -_ =  _
                             ; isRing = IsCommRing.isRing (CommRingStr.isCommRing (snd CRing))
                             }

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
  no-eta-equality
  private
    module R = CommRingStr R
    module S = CommRingStr S

  field
    pres0 : f R.0r ≡ S.0r
    pres1 : f R.1r ≡ S.1r
    pres+ : (x y : A) → f (x R.+ y) ≡ f x S.+ f y
    pres· : (x y : A) → f (x R.· y) ≡ f x S.· f y
    pres- : (x : A) → f (R.- x) ≡ S.- (f x)

unquoteDecl IsCommRingHomIsoΣ = declareRecordIsoΣ IsCommRingHomIsoΣ (quote IsCommRingHom)

CommRingHom : (R : CommRing ℓ) (S : CommRing ℓ') → Type (ℓ-max ℓ ℓ')
CommRingHom R S = Σ[ f ∈ (⟨ R ⟩ → ⟨ S ⟩) ] IsCommRingHom (R .snd) f (S .snd)

IsCommRingEquiv : {A : Type ℓ} {B : Type ℓ'}
  (R : CommRingStr A) (e : A ≃ B) (S : CommRingStr B) → Type (ℓ-max ℓ ℓ')
IsCommRingEquiv R e S = IsCommRingHom R (e .fst) S

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

isPropIsCommRingHom : {A : Type ℓ} {B : Type ℓ'} (R : CommRingStr A) (f : A → B) (S : CommRingStr B)
  → isProp (IsCommRingHom R f S)
isPropIsCommRingHom R f S = isOfHLevelRetractFromIso 1 IsCommRingHomIsoΣ
                        (isProp×4 (is-set _ _)
                                  (is-set _ _)
                                  (isPropΠ2 λ _ _ → is-set _ _)
                                  (isPropΠ2 λ _ _ → is-set _ _)
                                  (isPropΠ λ _ → is-set _ _))
  where
  open CommRingStr S using (is-set)

isSetCommRingHom : (R : CommRing ℓ) (S : CommRing ℓ') → isSet (CommRingHom R S)
isSetCommRingHom R S = isSetΣSndProp (isSetΠ λ _ → is-set) (λ f → isPropIsCommRingHom (snd R) f (snd S))
  where
  open CommRingStr (str S) using (is-set)

isSetCommRingEquiv : (A : CommRing ℓ) (B : CommRing ℓ') → isSet (CommRingEquiv A B)
isSetCommRingEquiv A B = isSetΣSndProp (isOfHLevel≃ 2 A.is-set B.is-set)
                                   (λ e → isPropIsCommRingHom (snd A) (fst e) (snd B))
  where
  module A = CommRingStr (str A)
  module B = CommRingStr (str B)

RingHom→CommRingHom : {R : CommRing ℓ} {S : CommRing ℓ'}
                     → RingHom (CommRing→Ring R) (CommRing→Ring S)
                     → CommRingHom R S
RingHom→CommRingHom f .fst = f .fst
RingHom→CommRingHom {R = R} {S = S} f .snd = copy
  where open IsCommRingHom
        copy : IsCommRingHom (R .snd) (f .fst) (S .snd)
        copy .pres0 = f .snd .IsRingHom.pres0
        copy .pres1 = f .snd .IsRingHom.pres1
        copy .pres+ = f .snd .IsRingHom.pres+
        copy .pres· = f .snd .IsRingHom.pres·
        copy .pres- = f .snd .IsRingHom.pres-

IsRingHom→IsCommRingHom : (R : CommRing ℓ) (S : CommRing ℓ')
                     → (f : ⟨ R ⟩ → ⟨ S ⟩)
                     → IsRingHom ((CommRing→Ring R) .snd) f ((CommRing→Ring S) .snd)
                     → IsCommRingHom (R .snd) f (S .snd)
IsRingHom→IsCommRingHom R S f p = RingHom→CommRingHom (f , p) .snd

CommRingHom→RingHom : {R : CommRing ℓ} {S : CommRing ℓ'}
                     → CommRingHom R S
                     → RingHom (CommRing→Ring R) (CommRing→Ring S)
CommRingHom→RingHom f .fst = f .fst
CommRingHom→RingHom {R = R} {S = S} f .snd = copy
  where open IsRingHom
        copy : IsRingHom ((CommRing→Ring R) .snd) (f .fst) ((CommRing→Ring S) .snd)
        copy .pres0 = f .snd .IsCommRingHom.pres0
        copy .pres1 = f .snd .IsCommRingHom.pres1
        copy .pres+ = f .snd .IsCommRingHom.pres+
        copy .pres· = f .snd .IsCommRingHom.pres·
        copy .pres- = f .snd .IsCommRingHom.pres-

IsCommRingHom→IsRingHom : (R : CommRing ℓ) (S : CommRing ℓ')
                     → (f : ⟨ R ⟩ → ⟨ S ⟩)
                     → IsCommRingHom (R .snd) f (S .snd)
                     → IsRingHom ((CommRing→Ring R) .snd) f ((CommRing→Ring S) .snd)
IsCommRingHom→IsRingHom R S f p = CommRingHom→RingHom (f , p) .snd

CommRingEquiv→RingEquiv : {A : CommRing ℓ} {B : CommRing ℓ'}
  → CommRingEquiv A B → RingEquiv (CommRing→Ring A) (CommRing→Ring B)
CommRingEquiv→RingEquiv e .fst = e .fst
CommRingEquiv→RingEquiv e .snd = IsCommRingHom→IsRingHom _ _ (e .fst .fst) (e .snd)

module _ {R : CommRing ℓ} {S : CommRing ℓ'} {f : ⟨ R ⟩ → ⟨ S ⟩} where

  private
    module R = CommRingStr (R .snd)
    module S = CommRingStr (S .snd)

  module _
    (p1 : f R.1r ≡ S.1r)
    (p+ : (x y : ⟨ R ⟩) → f (x R.+ y) ≡ f x S.+ f y)
    (p· : (x y : ⟨ R ⟩) → f (x R.· y) ≡ f x S.· f y)
    where

    makeIsCommRingHom : IsCommRingHom (R .snd) f (S .snd)
    makeIsCommRingHom = IsRingHom→IsCommRingHom _ _ _ (makeIsRingHom p1 p+ p·)

_$cr_ : {R : CommRing ℓ} {S : CommRing ℓ'} → (φ : CommRingHom R S) → (x : ⟨ R ⟩) → ⟨ S ⟩
φ $cr x = φ .fst x

opaque
  CommRingHom≡ : {R : CommRing ℓ} {S : CommRing ℓ'} {φ ψ : CommRingHom R S} → fst φ ≡ fst ψ → φ ≡ ψ
  CommRingHom≡ = Σ≡Prop λ f → isPropIsCommRingHom _ f _

  CommRingHomPathP : (R : CommRing ℓ) (S T : CommRing ℓ') (p : S ≡ T) (φ : CommRingHom R S) (ψ : CommRingHom R T)
               → PathP (λ i → R .fst → p i .fst) (φ .fst) (ψ .fst)
               → PathP (λ i → CommRingHom R (p i)) φ ψ
  CommRingHomPathP R S T p φ ψ q = ΣPathP (q , isProp→PathP (λ _ → isPropIsCommRingHom _ _ _) _ _)

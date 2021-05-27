{-# OPTIONS --safe #-}
module Cubical.Algebra.Algebra.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.SIP

open import Cubical.Data.Sigma

open import Cubical.Displayed.Base
open import Cubical.Displayed.Auto
open import Cubical.Displayed.Record
open import Cubical.Displayed.Universe

open import Cubical.Reflection.RecordEquiv

open import Cubical.Algebra.Module
open import Cubical.Algebra.Ring
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group
open import Cubical.Algebra.Monoid

open Iso

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level

record IsAlgebra (R : Ring ℓ) {A : Type ℓ'}
                 (0a 1a : A) (_+_ _·_ : A → A → A) (-_ : A → A)
                 (_⋆_ : ⟨ R ⟩ → A → A) : Type (ℓ-max ℓ ℓ') where

  constructor isalgebra

  open RingStr (snd R) using (1r) renaming (_+_ to _+r_; _·_ to _·r_)

  field
    isLeftModule : IsLeftModule R 0a _+_ -_ _⋆_
    ·-isMonoid  : IsMonoid 1a _·_
    dist        : (x y z : A) → (x · (y + z) ≡ (x · y) + (x · z))
                              × ((x + y) · z ≡ (x · z) + (y · z))
    ⋆-lassoc     : (r : ⟨ R ⟩) (x y : A) → (r ⋆ x) · y ≡ r ⋆ (x · y)
    ⋆-rassoc     : (r : ⟨ R ⟩) (x y : A) → r ⋆ (x · y) ≡ x · (r ⋆ y)

  open IsLeftModule isLeftModule public

  isRing : IsRing _ _ _ _ _
  isRing = isring (IsLeftModule.+-isAbGroup isLeftModule) ·-isMonoid dist
  open IsRing isRing public hiding (_-_; +Assoc; +Lid; +Linv; +Rid; +Rinv; +Comm)

unquoteDecl IsAlgebraIsoΣ = declareRecordIsoΣ IsAlgebraIsoΣ (quote IsAlgebra)

record AlgebraStr (R : Ring ℓ) (A : Type ℓ') : Type (ℓ-max ℓ ℓ') where

  constructor algebrastr

  field
    0a             : A
    1a             : A
    _+_            : A → A → A
    _·_            : A → A → A
    -_             : A → A
    _⋆_            : ⟨ R ⟩ → A → A
    isAlgebra      : IsAlgebra R 0a 1a _+_ _·_ -_ _⋆_

  open IsAlgebra isAlgebra public

Algebra : (R : Ring ℓ) → ∀ ℓ' → Type (ℓ-max ℓ (ℓ-suc ℓ'))
Algebra R ℓ' = Σ[ A ∈ Type ℓ' ] AlgebraStr R A

module commonExtractors {R : Ring ℓ} where

  Algebra→Module : (A : Algebra R ℓ') → LeftModule R ℓ'
  Algebra→Module (_ , algebrastr A _ _ _ _ _ (isalgebra isLeftModule _ _ _ _)) =
    _ , leftmodulestr A _ _ _ isLeftModule

  Algebra→Ring : (A : Algebra R ℓ') → Ring ℓ'
  Algebra→Ring (_ , str) = _ , ringstr _ _ _ _ _ (IsAlgebra.isRing (AlgebraStr.isAlgebra str))

  Algebra→AbGroup : (A : Algebra R ℓ') → AbGroup ℓ'
  Algebra→AbGroup A = LeftModule→AbGroup (Algebra→Module A)

  Algebra→Monoid : (A : Algebra R ℓ') → Monoid ℓ'
  Algebra→Monoid A = Ring→Monoid (Algebra→Ring A)

  isSetAlgebra : (A : Algebra R ℓ') → isSet ⟨ A ⟩
  isSetAlgebra A = isSetAbGroup (Algebra→AbGroup A)

  open RingStr (snd R) using (1r; ·Ldist+) renaming (_+_ to _+r_; _·_ to _·s_)

  makeIsAlgebra : {A : Type ℓ'} {0a 1a : A}
                  {_+_ _·_ : A → A → A} { -_ : A → A} {_⋆_ : ⟨ R ⟩ → A → A}
                  (isSet-A : isSet A)
                  (+-assoc :  (x y z : A) → x + (y + z) ≡ (x + y) + z)
                  (+-rid : (x : A) → x + 0a ≡ x)
                  (+-rinv : (x : A) → x + (- x) ≡ 0a)
                  (+-comm : (x y : A) → x + y ≡ y + x)
                  (·-assoc :  (x y z : A) → x · (y · z) ≡ (x · y) · z)
                  (·-rid : (x : A) → x · 1a ≡ x)
                  (·-lid : (x : A) → 1a · x ≡ x)
                  (·-rdist-+ : (x y z : A) → x · (y + z) ≡ (x · y) + (x · z))
                  (·-ldist-+ : (x y z : A) → (x + y) · z ≡ (x · z) + (y · z))
                  (⋆-assoc : (r s : ⟨ R ⟩) (x : A) → (r ·s s) ⋆ x ≡ r ⋆ (s ⋆ x))
                  (⋆-ldist : (r s : ⟨ R ⟩) (x : A) → (r +r s) ⋆ x ≡ (r ⋆ x) + (s ⋆ x))
                  (⋆-rdist : (r : ⟨ R ⟩) (x y : A) → r ⋆ (x + y) ≡ (r ⋆ x) + (r ⋆ y))
                  (⋆-lid   : (x : A) → 1r ⋆ x ≡ x)
                  (⋆-lassoc : (r : ⟨ R ⟩) (x y : A) → (r ⋆ x) · y ≡ r ⋆ (x · y))
                  (⋆-rassoc : (r : ⟨ R ⟩) (x y : A) → r ⋆ (x · y) ≡ x · (r ⋆ y))
                → IsAlgebra R 0a 1a _+_ _·_ -_ _⋆_
  makeIsAlgebra isSet-A
                +-assoc +-rid +-rinv +-comm
                ·-assoc ·-rid ·-lid ·-rdist-+ ·-ldist-+
                ⋆-assoc ⋆-ldist ⋆-rdist ⋆-lid ⋆-lassoc ⋆-rassoc =
                isalgebra
                  (makeIsLeftModule isSet-A
                                    +-assoc +-rid +-rinv +-comm
                                    ⋆-assoc ⋆-ldist ⋆-rdist ⋆-lid)
                  (makeIsMonoid isSet-A ·-assoc ·-rid ·-lid)
                  (λ x y z → ·-rdist-+ x y z , ·-ldist-+ x y z)
                  ⋆-lassoc ⋆-rassoc


open commonExtractors public

record IsAlgebraHom {R : Ring ℓ} {A : Type ℓ'} {B : Type ℓ''}
  (M : AlgebraStr R A) (f : A → B) (N : AlgebraStr R B)
  : Type (ℓ-max ℓ (ℓ-max ℓ' ℓ''))
  where

  -- Shorter qualified names
  private
    module M = AlgebraStr M
    module N = AlgebraStr N

  field
    pres0 : f M.0a ≡ N.0a
    pres1 : f M.1a ≡ N.1a
    pres+ : (x y : A) → f (x M.+ y) ≡ f x N.+ f y
    pres· : (x y : A) → f (x M.· y) ≡ f x N.· f y
    pres- : (x : A) → f (M.- x) ≡ N.- (f x)
    pres⋆ : (r : ⟨ R ⟩) (y : A) → f (r M.⋆ y) ≡ r N.⋆ f y

open IsAlgebraHom

AlgebraHom : {R : Ring ℓ} (M : Algebra R ℓ') (N : Algebra R ℓ'') → Type (ℓ-max ℓ (ℓ-max ℓ' ℓ''))
AlgebraHom M N = Σ[ f ∈ (⟨ M ⟩ → ⟨ N ⟩) ] IsAlgebraHom (M .snd) f (N .snd)

IsAlgebraEquiv : {R : Ring ℓ} {A B : Type ℓ'}
  (M : AlgebraStr R A) (e : A ≃ B) (N : AlgebraStr R B)
  → Type (ℓ-max ℓ ℓ')
IsAlgebraEquiv M e N = IsAlgebraHom M (e .fst) N

AlgebraEquiv : {R : Ring ℓ} (M N : Algebra R ℓ') → Type (ℓ-max ℓ ℓ')
AlgebraEquiv M N = Σ[ e ∈ ⟨ M ⟩ ≃ ⟨ N ⟩ ] IsAlgebraEquiv (M .snd) e (N .snd)

_$a_ : {R : Ring ℓ} {A : Algebra R ℓ'} {B : Algebra R ℓ''} → AlgebraHom A B → ⟨ A ⟩ → ⟨ B ⟩
f $a x = fst f x

isPropIsAlgebra : (R : Ring ℓ) {A : Type ℓ'}
  (0a 1a : A)
  (_+_ _·_ : A → A → A)
  (-_ : A → A)
  (_⋆_ : ⟨ R ⟩ → A → A)
  → isProp (IsAlgebra R 0a 1a _+_ _·_ -_ _⋆_)
isPropIsAlgebra R _ _ _ _ _ _ =
  isOfHLevelRetractFromIso 1 IsAlgebraIsoΣ
    (isPropΣ
      (isPropIsLeftModule _ _ _ _ _)
      (λ mo →
        isProp× (isPropIsMonoid _ _)
          (isProp× (isPropΠ3 λ _ _ _ → isProp× (mo .is-set _ _) (mo .is-set _ _))
            (isProp× (isPropΠ3 λ _ _ _ → mo .is-set _ _)
              (isPropΠ3 λ _ _ _ → mo .is-set _ _)))))
  where
  open IsLeftModule

𝒮ᴰ-Algebra : (R : Ring ℓ) → DUARel (𝒮-Univ ℓ') (AlgebraStr R) (ℓ-max ℓ ℓ')
𝒮ᴰ-Algebra R =
  𝒮ᴰ-Record (𝒮-Univ _) (IsAlgebraEquiv {R = R})
    (fields:
      data[ 0a ∣ nul ∣ pres0 ]
      data[ 1a ∣ nul ∣ pres1 ]
      data[ _+_ ∣ bin ∣ pres+ ]
      data[ _·_ ∣ bin ∣ pres· ]
      data[ -_ ∣ autoDUARel _ _ ∣ pres- ]
      data[ _⋆_ ∣ autoDUARel _ _ ∣ pres⋆ ]
      prop[ isAlgebra ∣ (λ _ _ → isPropIsAlgebra _ _ _ _ _ _ _) ])
  where
  open AlgebraStr

  -- faster with some sharing
  nul = autoDUARel (𝒮-Univ _) (λ A → A)
  bin = autoDUARel (𝒮-Univ _) (λ A → A → A → A)

AlgebraPath : {R : Ring ℓ} (A B : Algebra R ℓ') → (AlgebraEquiv A B) ≃ (A ≡ B)
AlgebraPath {R = R} = ∫ (𝒮ᴰ-Algebra R) .UARel.ua

compIsAlgebraHom : {R : Ring ℓ} {A : Algebra R ℓ'} {B : Algebra R ℓ''} {C : Algebra R ℓ'''}
  {g : ⟨ B ⟩ → ⟨ C ⟩} {f : ⟨ A ⟩ → ⟨ B ⟩}
  → IsAlgebraHom (B .snd) g (C .snd)
  → IsAlgebraHom (A .snd) f (B .snd)
  → IsAlgebraHom (A .snd) (g ∘ f) (C .snd)
compIsAlgebraHom {g = g} {f} gh fh .pres0 = cong g (fh .pres0) ∙ gh .pres0
compIsAlgebraHom {g = g} {f} gh fh .pres1 = cong g (fh .pres1) ∙ gh .pres1
compIsAlgebraHom {g = g} {f} gh fh .pres+ x y = cong g (fh .pres+ x y) ∙ gh .pres+ (f x) (f y)
compIsAlgebraHom {g = g} {f} gh fh .pres· x y = cong g (fh .pres· x y) ∙ gh .pres· (f x) (f y)
compIsAlgebraHom {g = g} {f} gh fh .pres- x = cong g (fh .pres- x) ∙ gh .pres- (f x)
compIsAlgebraHom {g = g} {f} gh fh .pres⋆ r x = cong g (fh .pres⋆ r x) ∙ gh .pres⋆ r (f x)

_∘a_ : {R : Ring ℓ} {A : Algebra R ℓ'} {B : Algebra R ℓ''} {C : Algebra R ℓ'''}
       → AlgebraHom B C → AlgebraHom A B → AlgebraHom A C
_∘a_  g f .fst = g .fst ∘ f .fst
_∘a_  g f .snd = compIsAlgebraHom (g .snd) (f .snd)

module AlgebraTheory (R : Ring ℓ) (A : Algebra R ℓ') where
  open RingStr (snd R) renaming (_+_ to _+r_)
  open AlgebraStr (A .snd)

  0-actsNullifying : (x : ⟨ A ⟩) → 0r ⋆ x ≡ 0a
  0-actsNullifying x =
    let idempotent-+ = 0r ⋆ x              ≡⟨ cong (λ u → u ⋆ x) (sym (RingTheory.0Idempotent R)) ⟩
                       (0r +r 0r) ⋆ x      ≡⟨ ⋆-ldist 0r 0r x ⟩
                       (0r ⋆ x) + (0r ⋆ x) ∎
    in RingTheory.+Idempotency→0 (Algebra→Ring A) (0r ⋆ x) idempotent-+

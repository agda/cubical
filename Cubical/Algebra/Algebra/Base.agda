{-# OPTIONS --cubical --safe --no-import-sorts #-}
module Cubical.Algebra.Algebra.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.SIP

open import Cubical.Data.Sigma

open import Cubical.Structures.Axioms
open import Cubical.Structures.Auto
open import Cubical.Structures.Macro
open import Cubical.Algebra.Module
open import Cubical.Algebra.Ring
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group
open import Cubical.Algebra.Monoid

open Iso

private
  variable
    ℓ : Level

record IsAlgebra (R : Ring {ℓ}) {A : Type ℓ}
                 (0a 1a : A) (_+_ _·_ : A → A → A) (-_ : A → A)
                 (_⋆_ : ⟨ R ⟩ → A → A) : Type ℓ where

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
  open IsRing isRing public hiding (_-_; +-assoc; +-lid; +-linv; +-rid; +-rinv; +-comm)

record Algebra (R : Ring {ℓ}) : Type (ℓ-suc ℓ) where

  constructor algebra

  field
    Carrier        : Type ℓ
    0a             : Carrier
    1a             : Carrier
    _+_            : Carrier → Carrier → Carrier
    _·_            : Carrier → Carrier → Carrier
    -_             : Carrier → Carrier
    _⋆_            : ⟨ R ⟩ → Carrier → Carrier
    isAlgebra      : IsAlgebra R 0a 1a _+_ _·_ -_ _⋆_

  open IsAlgebra isAlgebra public


module commonExtractors {R : Ring {ℓ}} where
  ⟨_⟩a : Algebra R → Type ℓ
  ⟨_⟩a = Algebra.Carrier

  Algebra→Module : (A : Algebra R) → LeftModule R
  Algebra→Module (algebra A _ _ _ _ _ _ (isalgebra isLeftModule _ _ _ _)) =
    leftmodule A _ _ _ _ isLeftModule

  Algebra→Ring : (A : Algebra R) → Ring {ℓ}
  Algebra→Ring A = _ , ringstr _ _ _ _ _ (IsAlgebra.isRing (Algebra.isAlgebra A))

  Algebra→AbGroup : (A : Algebra R) → AbGroup {ℓ}
  Algebra→AbGroup A = LeftModule→AbGroup (Algebra→Module A)

  Algebra→Monoid : (A : Algebra R) → Monoid {ℓ}
  Algebra→Monoid A = Ring→Monoid (Algebra→Ring A)

  isSetAlgebra : (A : Algebra R) → isSet ⟨ A ⟩a
  isSetAlgebra A = isSetAbGroup (Algebra→AbGroup A)

  open RingStr (snd R) using (1r; ·-ldist-+) renaming (_+_ to _+r_; _·_ to _·s_)

  makeIsAlgebra : {A : Type ℓ} {0a 1a : A}
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

record AlgebraEquiv {R : Ring {ℓ}} (A B : Algebra R) : Type ℓ where

  constructor algebraiso

  instance
    _ : Algebra R
    _ = A
    _ : Algebra R
    _ = B

  open Algebra {{...}}

  field
    e      : ⟨ A ⟩a ≃ ⟨ B ⟩a
    isHom+ : (x y : ⟨ A ⟩a) → equivFun e (x + y) ≡ equivFun e x + equivFun e y
    isHom· : (x y : ⟨ A ⟩a) → equivFun e (x · y) ≡ equivFun e x · equivFun e y
    pres1  : equivFun e 1a ≡ 1a
    comm⋆  : (r : ⟨ R ⟩) (x : ⟨ A ⟩a) → equivFun e (r ⋆ x) ≡ r ⋆ equivFun e x

record AlgebraHom {R : Ring {ℓ}} (A B : Algebra R) : Type ℓ where

  constructor algebrahom

  private
    instance
      _ : Algebra R
      _ = A
      _ : Algebra R
      _ = B

  open Algebra {{...}}

  field
    f      : ⟨ A ⟩a → ⟨ B ⟩a
    isHom+ : (x y : ⟨ A ⟩a) → f (x + y) ≡ f x + f y
    isHom· : (x y : ⟨ A ⟩a) → f (x · y) ≡ f x · f y
    pres1  : f 1a ≡ 1a
    comm⋆  : (r : ⟨ R ⟩) (x : ⟨ A ⟩a) → f (r ⋆ x) ≡ r ⋆ f x

  pres0 : f 0a ≡ 0a
  pres0 = Theory.+-idempotency→0 (Algebra→Ring B) (f 0a)
          (f 0a        ≡⟨ cong f (sym (+-rid _)) ⟩
           f (0a + 0a) ≡⟨ isHom+ _ _ ⟩
           f 0a + f 0a ∎)

  isHom- : (x : ⟨ A ⟩a) → f (- x) ≡ - f x
  isHom- x = Theory.implicitInverse (Algebra→Ring B) (f x) (f (- x))
             (f (x) + f (- x)  ≡⟨ sym (isHom+ _ _) ⟩
             f (x - x)         ≡⟨ cong f (+-rinv _) ⟩
             f 0a              ≡⟨ pres0 ⟩
             0a ∎)

_$a_ : {R : Ring {ℓ}} {A B : Algebra R} → AlgebraHom A B → ⟨ A ⟩a → ⟨ B ⟩a
f $a x = AlgebraHom.f f x


_∘a_ : {R : Ring {ℓ}} {A B C : Algebra R}
       → AlgebraHom B C → AlgebraHom A B → AlgebraHom A C
_∘a_ {ℓ} {R} {A} {B} {C}
  (algebrahom f isHom+f isHom·f pres1f comm⋆f)
  (algebrahom g isHom+g isHom·g pres1g comm⋆g)
  =
  let
    open Algebra ⦃...⦄
    instance
      _ : Algebra R
      _ = A
      _ : Algebra R
      _ = B
      _ : Algebra R
      _ = C
  in algebrahom (f ∘ g)
    (λ x y → f (g (x + y))      ≡⟨ cong f (isHom+g x y) ⟩
             f (g x + g y)      ≡⟨ isHom+f _ _  ⟩
             f (g x) + f (g y)  ∎)
    (λ x y → f (g (x · y))      ≡⟨ cong f (isHom·g x y) ⟩
             f (g x · g y)      ≡⟨ isHom·f _ _  ⟩
             f (g x) · f (g y)  ∎)
    (f (g 1a) ≡⟨ cong f pres1g ⟩ f 1a ≡⟨ pres1f ⟩ 1a ∎)
    λ r x → f (g (r ⋆ x))  ≡⟨ cong f (comm⋆g _ _) ⟩
            f (r ⋆ (g x))  ≡⟨ comm⋆f _ _ ⟩
            r ⋆ (f (g x))  ∎


module AlgebraΣTheory (R : Ring {ℓ}) where

  RawAlgebraStructure = λ (A : Type ℓ) → (A → A → A) × (A → A → A) × A × (⟨ R ⟩ → A → A)

  RawAlgebraEquivStr = AutoEquivStr RawAlgebraStructure

  rawAlgebraUnivalentStr : UnivalentStr _ RawAlgebraEquivStr
  rawAlgebraUnivalentStr = autoUnivalentStr RawAlgebraStructure

  open RingStr (snd R) using (1r) renaming (_+_ to _+r_; _·_ to _·r_)
  open RingΣTheory
  open LeftModuleΣTheory R
  open MonoidΣTheory

  AlgebraAxioms : (A : Type ℓ) (str : RawAlgebraStructure A) → Type ℓ
  AlgebraAxioms A (_+_ , _·_ , 1a , _⋆_) =
               LeftModuleAxioms A (_+_ , _⋆_)
               × (MonoidAxioms A (1a , _·_))
               × ((x y z : A) → (x · (y + z) ≡ (x · y) + (x · z))
                              × ((x + y) · z ≡ (x · z) + (y · z)))
               × ((r : ⟨ R ⟩) (x y : A) → (r ⋆ x) · y ≡ r ⋆ (x · y))
               × ((r : ⟨ R ⟩) (x y : A) → r ⋆ (x · y) ≡ x · (r ⋆ y))

  AlgebraStructure : Type ℓ → Type ℓ
  AlgebraStructure = AxiomsStructure RawAlgebraStructure AlgebraAxioms

  AlgebraΣ : Type (ℓ-suc ℓ)
  AlgebraΣ = TypeWithStr ℓ AlgebraStructure

  AlgebraEquivStr : StrEquiv AlgebraStructure ℓ
  AlgebraEquivStr = AxiomsEquivStr RawAlgebraEquivStr AlgebraAxioms

  isSetAlgebraΣ : (A : AlgebraΣ) → isSet _
  isSetAlgebraΣ (A , _ , (isLeftModule , _ , _) ) = isSetLeftModuleΣ (A , _ , isLeftModule)

  isPropAlgebraAxioms : (A : Type ℓ) (s : RawAlgebraStructure A)
                             → isProp (AlgebraAxioms A s)
  isPropAlgebraAxioms A (_+_ , _·_ , 1a , _⋆_) =
    isPropΣ (isPropLeftModuleAxioms A (_+_ , _⋆_))
    (λ isLeftModule →
     isProp× (isPropMonoidAxioms A (1a , _·_))
    (isProp× (isPropΠ3 (λ _ _ _ → isProp× ((isSetLeftModuleΣ (A , _ , isLeftModule)) _ _)
                                          ((isSetLeftModuleΣ (A , _ , isLeftModule)) _ _)))
    (isProp× (isPropΠ3 (λ _ _ _ → (isSetLeftModuleΣ (A , _ , isLeftModule)) _ _))
             (isPropΠ3 (λ _ _ _ → (isSetLeftModuleΣ (A , _ , isLeftModule)) _ _)))))

  Algebra→AlgebraΣ : Algebra R → AlgebraΣ
  Algebra→AlgebraΣ (algebra A 0a 1a _+_ _·_ -_ _⋆_
                            (isalgebra isLeftModule isMonoid dist ⋆-lassoc ⋆-rassoc)) =
    A , (_+_ , _·_ , 1a , _⋆_) ,
    (LeftModule→LeftModuleΣ (leftmodule A _ _ _ _ isLeftModule) .snd .snd) ,
    Monoid→MonoidΣ (monoid A _ _ isMonoid) .snd .snd ,
    dist ,
    ⋆-lassoc ,
    ⋆-rassoc

  AlgebraΣ→Algebra : AlgebraΣ → Algebra R
  AlgebraΣ→Algebra (A , (_+_ , _·_ , 1a , _⋆_) , isLeftModule , isMonoid , dist , lassoc , rassoc) =
    algebra A _ 1a _+_ _·_ _ _⋆_
    (isalgebra (LeftModule.isLeftModule (LeftModuleΣ→LeftModule (A , (_ , isLeftModule))))
               (MonoidStr.isMonoid (MonoidΣ→Monoid (A , (_ , isMonoid)) .snd))
               dist lassoc rassoc)

  AlgebraIsoAlgebraΣ : Iso (Algebra R) AlgebraΣ
  AlgebraIsoAlgebraΣ = iso Algebra→AlgebraΣ AlgebraΣ→Algebra (λ _ → refl) (λ _ → refl)

  algebraUnivalentStr : UnivalentStr AlgebraStructure AlgebraEquivStr
  algebraUnivalentStr = axiomsUnivalentStr _ isPropAlgebraAxioms rawAlgebraUnivalentStr

  AlgebraΣPath : (M N : AlgebraΣ) → (M ≃[ AlgebraEquivStr ] N) ≃ (M ≡ N)
  AlgebraΣPath = SIP algebraUnivalentStr

  AlgebraEquivΣ : (M N : Algebra R) → Type ℓ
  AlgebraEquivΣ M N = Algebra→AlgebraΣ M ≃[ AlgebraEquivStr ] Algebra→AlgebraΣ N

  AlgebraEquivΣPath : {M N : Algebra R} → Iso (AlgebraEquiv M N) (AlgebraEquivΣ M N)
  fun AlgebraEquivΣPath (algebraiso e isHom+ isHom· pres1 comm⋆) =
    e , isHom+ , (isHom· , (pres1 , comm⋆))
  inv AlgebraEquivΣPath (f , isHom+ , isHom· , pres1 , comm⋆) =
    algebraiso f isHom+ isHom· pres1 comm⋆
  rightInv AlgebraEquivΣPath _ = refl
  leftInv AlgebraEquivΣPath _ = refl

  AlgebraPath : (M N : Algebra R) → (AlgebraEquiv M N) ≃ (M ≡ N)
  AlgebraPath M N =
    AlgebraEquiv M N                                    ≃⟨ isoToEquiv AlgebraEquivΣPath ⟩
    AlgebraEquivΣ M N                                   ≃⟨ AlgebraΣPath _ _ ⟩
    Algebra→AlgebraΣ M ≡ Algebra→AlgebraΣ N             ≃⟨ isoToEquiv
                                                             (invIso
                                                             (congIso
                                                             AlgebraIsoAlgebraΣ))
                                                           ⟩
    M ≡ N ■

AlgebraPath : {R : Ring {ℓ}} (M N : Algebra R) → (AlgebraEquiv M N) ≃ (M ≡ N)
AlgebraPath {ℓ} {R} = AlgebraΣTheory.AlgebraPath R

module AlgebraTheory (R : Ring {ℓ}) (A : Algebra R) where
  open RingStr (snd R) renaming (_+_ to _+r_)
  open Algebra A

  0-actsNullifying : (x : ⟨ A ⟩a) → 0r ⋆ x ≡ 0a
  0-actsNullifying x =
    let idempotent-+ = 0r ⋆ x              ≡⟨ cong (λ u → u ⋆ x) (sym (Theory.0-idempotent R)) ⟩
                       (0r +r 0r) ⋆ x      ≡⟨ ⋆-ldist 0r 0r x ⟩
                       (0r ⋆ x) + (0r ⋆ x) ∎
    in Theory.+-idempotency→0 (Algebra→Ring A) (0r ⋆ x) idempotent-+

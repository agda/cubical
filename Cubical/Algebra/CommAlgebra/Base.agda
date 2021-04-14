{-# OPTIONS --cubical --safe --no-import-sorts #-}
module Cubical.Algebra.CommAlgebra.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.SIP

open import Cubical.Data.Sigma

open import Cubical.Reflection.StrictEquiv

open import Cubical.Structures.Axioms
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring
open import Cubical.Algebra.Algebra hiding (⟨_⟩a)
open import Cubical.Algebra.Algebra using (_$a_; AlgebraHom; isSetAlgebra) public

private
  variable
    ℓ ℓ′ : Level

record IsCommAlgebra (R : CommRing {ℓ}) {A : Type ℓ}
                     (0a : A) (1a : A)
                     (_+_ : A → A → A) (_·_ : A → A → A) (-_ : A → A)
                     (_⋆_ : ⟨ R ⟩ → A → A) : Type ℓ where

  constructor iscommalgebra

  field
    isAlgebra : IsAlgebra (CommRing→Ring R) 0a 1a _+_ _·_ -_ _⋆_
    ·-comm    : (x y : A) → x · y ≡ y · x

  open IsAlgebra isAlgebra public

record CommAlgebra (R : CommRing {ℓ}) : Type (ℓ-suc ℓ) where

  constructor commalgebra

  field
    Carrier        : Type ℓ
    0a             : Carrier
    1a             : Carrier
    _+_            : Carrier → Carrier → Carrier
    _·_            : Carrier → Carrier → Carrier
    -_             : Carrier → Carrier
    _⋆_            : ⟨ R ⟩ → Carrier → Carrier
    isCommAlgebra  : IsCommAlgebra R 0a 1a _+_ _·_ -_ _⋆_

  infix  8 -_
  infixl 7 _·_
  infixl 7 _⋆_
  infixl 6 _+_

  open IsCommAlgebra isCommAlgebra public

module _ {R : CommRing {ℓ}} where
  open CommRingStr (snd R) using (1r) renaming (_+_ to _+r_; _·_ to _·s_)

  ⟨_⟩a : CommAlgebra R → Type ℓ
  ⟨_⟩a = CommAlgebra.Carrier

  CommAlgebra→Algebra : (A : CommAlgebra R) → Algebra (CommRing→Ring R)
  CommAlgebra→Algebra (commalgebra Carrier _ _ _ _ _ _ (iscommalgebra isAlgebra ·-comm)) =
    algebra Carrier _ _ _ _ _ _ isAlgebra

  CommAlgebra→CommRing : (A : CommAlgebra R) → CommRing {ℓ}
  CommAlgebra→CommRing (commalgebra Carrier _ _ _ _ _ _
                          (iscommalgebra isAlgebra ·-comm)) =
    _ , commringstr _ _ _ _ _ (iscommring (IsAlgebra.isRing isAlgebra) ·-comm)

  CommAlgebraEquiv : (R S : CommAlgebra R) → Type ℓ
  CommAlgebraEquiv R S = AlgebraEquiv (CommAlgebra→Algebra R) (CommAlgebra→Algebra S)

  makeIsCommAlgebra : {A : Type ℓ} {0a 1a : A}
                      {_+_ _·_ : A → A → A} { -_ : A → A} {_⋆_ : ⟨ R ⟩ → A → A}
                      (isSet-A : isSet A)
                      (+-assoc :  (x y z : A) → x + (y + z) ≡ (x + y) + z)
                      (+-rid : (x : A) → x + 0a ≡ x)
                      (+-rinv : (x : A) → x + (- x) ≡ 0a)
                      (+-comm : (x y : A) → x + y ≡ y + x)
                      (·-assoc :  (x y z : A) → x · (y · z) ≡ (x · y) · z)
                      (·-lid : (x : A) → 1a · x ≡ x)
                      (·-ldist-+ : (x y z : A) → (x + y) · z ≡ (x · z) + (y · z))
                      (·-comm : (x y : A) → x · y ≡ y · x)
                      (⋆-assoc : (r s : ⟨ R ⟩) (x : A) → (r ·s s) ⋆ x ≡ r ⋆ (s ⋆ x))
                      (⋆-ldist : (r s : ⟨ R ⟩) (x : A) → (r +r s) ⋆ x ≡ (r ⋆ x) + (s ⋆ x))
                      (⋆-rdist : (r : ⟨ R ⟩) (x y : A) → r ⋆ (x + y) ≡ (r ⋆ x) + (r ⋆ y))
                      (⋆-lid   : (x : A) → 1r ⋆ x ≡ x)
                      (⋆-lassoc : (r : ⟨ R ⟩) (x y : A) → (r ⋆ x) · y ≡ r ⋆ (x · y))
                    → IsCommAlgebra R 0a 1a _+_ _·_ -_ _⋆_
  makeIsCommAlgebra {A} {0a} {1a} {_+_} {_·_} { -_} {_⋆_} isSet-A
                    +-assoc +-rid +-rinv +-comm
                    ·-assoc ·-lid ·-ldist-+ ·-comm
                    ⋆-assoc ⋆-ldist ⋆-rdist ⋆-lid ⋆-lassoc
   = iscommalgebra
     (makeIsAlgebra
       isSet-A
       +-assoc +-rid +-rinv +-comm
       ·-assoc
         (λ x → x · 1a ≡⟨ ·-comm _ _ ⟩ 1a · x ≡⟨ ·-lid _ ⟩ x ∎)
         ·-lid
         (λ x y z → x · (y + z)       ≡⟨ ·-comm _ _ ⟩
                    (y + z) · x       ≡⟨ ·-ldist-+ _ _ _ ⟩
                    (y · x) + (z · x) ≡⟨ cong (λ u → (y · x) + u) (·-comm _ _) ⟩
                    (y · x) + (x · z) ≡⟨ cong (λ u → u + (x · z)) (·-comm _ _) ⟩
                    (x · y) + (x · z) ∎)
         ·-ldist-+
       ⋆-assoc
         ⋆-ldist
         ⋆-rdist
         ⋆-lid
         ⋆-lassoc
         λ r x y → r ⋆ (x · y) ≡⟨ cong (λ u → r ⋆ u) (·-comm _ _) ⟩
                   r ⋆ (y · x) ≡⟨ sym (⋆-lassoc _ _ _) ⟩
                   (r ⋆ y) · x ≡⟨ ·-comm _ _ ⟩
                   x · (r ⋆ y) ∎)
     ·-comm


module _ {R : CommRing {ℓ}} ((S , str) : CommRing {ℓ}) where
  open CommRingStr {{...}}
  instance
    _ : CommRingStr _
    _ = str
    _ : CommRingStr _
    _ = snd R

  commAlgebraFromCommRing :
        (_⋆_ : fst R → S → S)
      → ((r s : fst R) (x : S) → (r · s) ⋆ x ≡ r ⋆ (s ⋆ x))
      → ((r s : fst R) (x : S) → (r + s) ⋆ x ≡ (r ⋆ x) + (s ⋆ x))
      → ((r : fst R) (x y : S) → r ⋆ (x + y) ≡ (r ⋆ x) + (r ⋆ y))
      → ((x : S) → 1r ⋆ x ≡ x)
      → ((r : fst R) (x y : S) → (r ⋆ x) · y ≡ r ⋆ (x · y))
      → CommAlgebra R
  commAlgebraFromCommRing _⋆_ ·Assoc⋆ ⋆DistR ⋆DistL ⋆Lid ⋆Assoc· =
    commalgebra S 0r 1r _+_ _·_  -_ _⋆_
      (makeIsCommAlgebra is-set +Assoc +Rid +Rinv +Comm ·Assoc ·Lid ·Ldist+ ·-comm
                                ·Assoc⋆ ⋆DistR ⋆DistL ⋆Lid ⋆Assoc·)


module CommAlgebraΣTheory (R : CommRing {ℓ}) where

  open AlgebraΣTheory (CommRing→Ring R)

  CommAlgebraAxioms : (A : Type ℓ) (s : RawAlgebraStructure A) → Type ℓ
  CommAlgebraAxioms A (_+_ , _·_ , 1a , _⋆_) = AlgebraAxioms A (_+_ , _·_ , 1a , _⋆_)
                                      × ((x y : A) → x · y ≡ y · x)

  CommAlgebraStructure : Type ℓ → Type ℓ
  CommAlgebraStructure = AxiomsStructure RawAlgebraStructure CommAlgebraAxioms

  CommAlgebraΣ : Type (ℓ-suc ℓ)
  CommAlgebraΣ = TypeWithStr ℓ CommAlgebraStructure

  CommAlgebraEquivStr : StrEquiv CommAlgebraStructure ℓ
  CommAlgebraEquivStr = AxiomsEquivStr RawAlgebraEquivStr CommAlgebraAxioms

  isPropCommAlgebraAxioms : (A : Type ℓ) (s : RawAlgebraStructure A)
                       → isProp (CommAlgebraAxioms A s)
  isPropCommAlgebraAxioms A (_+_ , _·_ , 1a , _⋆_) =
    isPropΣ (isPropAlgebraAxioms A (_+_ , _·_ , 1a , _⋆_))
           λ isAlgebra → isPropΠ2 λ _ _ → (isSetAlgebraΣ (A , _ , isAlgebra)) _ _

  CommAlgebra→CommAlgebraΣ : CommAlgebra R → CommAlgebraΣ
  CommAlgebra→CommAlgebraΣ (commalgebra _ _ _ _ _ _ _ (iscommalgebra G C)) =
    _ , _ , Algebra→AlgebraΣ (algebra _ _ _ _ _ _ _ G) .snd .snd , C

  CommAlgebraΣ→CommAlgebra : CommAlgebraΣ → CommAlgebra R
  CommAlgebraΣ→CommAlgebra (_ , _ , G , C) =
    commalgebra _ _ _ _ _ _ _ (iscommalgebra (AlgebraΣ→Algebra (_ , _ , G) .Algebra.isAlgebra) C)

  CommAlgebraIsoCommAlgebraΣ : Iso (CommAlgebra R) CommAlgebraΣ
  CommAlgebraIsoCommAlgebraΣ =
    iso CommAlgebra→CommAlgebraΣ CommAlgebraΣ→CommAlgebra (λ _ → refl) (λ _ → refl)

  commAlgebraUnivalentStr : UnivalentStr CommAlgebraStructure CommAlgebraEquivStr
  commAlgebraUnivalentStr = axiomsUnivalentStr _ isPropCommAlgebraAxioms rawAlgebraUnivalentStr

  CommAlgebraΣPath : (A B : CommAlgebraΣ) → (A ≃[ CommAlgebraEquivStr ] B) ≃ (A ≡ B)
  CommAlgebraΣPath = SIP commAlgebraUnivalentStr

  CommAlgebraEquivΣ : (A B : CommAlgebra R) → Type ℓ
  CommAlgebraEquivΣ A B = CommAlgebra→CommAlgebraΣ A ≃[ CommAlgebraEquivStr ] CommAlgebra→CommAlgebraΣ B

  CommAlgebraPath : (A B : CommAlgebra R) → (CommAlgebraEquiv A B) ≃ (A ≡ B)
  CommAlgebraPath A B =
    CommAlgebraEquiv A B   ≃⟨ strictIsoToEquiv AlgebraEquivΣPath ⟩
    CommAlgebraEquivΣ A B  ≃⟨ CommAlgebraΣPath _ _ ⟩
    CommAlgebra→CommAlgebraΣ A ≡ CommAlgebra→CommAlgebraΣ B
      ≃⟨ isoToEquiv (invIso (congIso CommAlgebraIsoCommAlgebraΣ)) ⟩
    A ≡ B ■

CommAlgebraPath : (R : CommRing {ℓ}) → (A B : CommAlgebra R) → (CommAlgebraEquiv A B) ≃ (A ≡ B)
CommAlgebraPath = CommAlgebraΣTheory.CommAlgebraPath

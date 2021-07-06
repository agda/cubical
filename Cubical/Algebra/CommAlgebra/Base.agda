{-# OPTIONS --safe #-}
module Cubical.Algebra.CommAlgebra.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.SIP

open import Cubical.Data.Sigma

open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring
open import Cubical.Algebra.Algebra

open import Cubical.Displayed.Base
open import Cubical.Displayed.Auto
open import Cubical.Displayed.Record
open import Cubical.Displayed.Universe

open import Cubical.Reflection.RecordEquiv

private
  variable
    ℓ ℓ' : Level

record IsCommAlgebra (R : CommRing ℓ) {A : Type ℓ'}
                     (0a : A) (1a : A)
                     (_+_ : A → A → A) (_·_ : A → A → A) (-_ : A → A)
                     (_⋆_ : ⟨ R ⟩ → A → A) : Type (ℓ-max ℓ ℓ') where

  constructor iscommalgebra

  field
    isAlgebra : IsAlgebra (CommRing→Ring R) 0a 1a _+_ _·_ -_ _⋆_
    ·-comm    : (x y : A) → x · y ≡ y · x

  open IsAlgebra isAlgebra public

unquoteDecl IsCommAlgebraIsoΣ = declareRecordIsoΣ IsCommAlgebraIsoΣ (quote IsCommAlgebra)

record CommAlgebraStr (R : CommRing ℓ) (A : Type ℓ') : Type (ℓ-max ℓ ℓ') where

  constructor commalgebrastr

  field
    0a             : A
    1a             : A
    _+_            : A → A → A
    _·_            : A → A → A
    -_             : A → A
    _⋆_            : ⟨ R ⟩ → A → A
    isCommAlgebra      : IsCommAlgebra R 0a 1a _+_ _·_ -_ _⋆_

  open IsCommAlgebra isCommAlgebra public

CommAlgebra : (R : CommRing ℓ) → ∀ ℓ' → Type (ℓ-max ℓ (ℓ-suc ℓ'))
CommAlgebra R ℓ' = Σ[ A ∈ Type ℓ' ] CommAlgebraStr R A

module _ {R : CommRing ℓ} where
  open CommRingStr (snd R) using (1r) renaming (_+_ to _+r_; _·_ to _·s_)

  CommAlgebraStr→AlgebraStr : {A : Type ℓ'} → CommAlgebraStr R A → AlgebraStr (CommRing→Ring R) A
  CommAlgebraStr→AlgebraStr (commalgebrastr _ _ _ _ _ _ (iscommalgebra isAlgebra ·-comm)) =
    algebrastr _ _ _ _ _ _ isAlgebra

  CommAlgebra→Algebra : (A : CommAlgebra R ℓ') → Algebra (CommRing→Ring R) ℓ'
  CommAlgebra→Algebra (_ , str) = (_ , CommAlgebraStr→AlgebraStr str)

  CommAlgebra→CommRing : (A : CommAlgebra R ℓ') → CommRing ℓ'
  CommAlgebra→CommRing (_ , commalgebrastr  _ _ _ _ _ _ (iscommalgebra isAlgebra ·-comm)) =
    _ , commringstr _ _ _ _ _ (iscommring (IsAlgebra.isRing isAlgebra) ·-comm)

  isSetCommAlgebra : (A : CommAlgebra R ℓ') → isSet ⟨ A ⟩
  isSetCommAlgebra A = isSetAlgebra (CommAlgebra→Algebra A)

  makeIsCommAlgebra : {A : Type ℓ'} {0a 1a : A}
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
  makeIsCommAlgebra {A = A} {0a} {1a} {_+_} {_·_} { -_} {_⋆_} isSet-A
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

  IsCommAlgebraEquiv : {A B : Type ℓ'}
    (M : CommAlgebraStr R A) (e : A ≃ B) (N : CommAlgebraStr R B)
    → Type (ℓ-max ℓ ℓ')
  IsCommAlgebraEquiv M e N =
    IsAlgebraHom (CommAlgebraStr→AlgebraStr M) (e .fst) (CommAlgebraStr→AlgebraStr N)

  CommAlgebraEquiv : (M N : CommAlgebra R ℓ') → Type (ℓ-max ℓ ℓ')
  CommAlgebraEquiv M N = Σ[ e ∈ ⟨ M ⟩ ≃ ⟨ N ⟩ ] IsCommAlgebraEquiv (M .snd) e (N .snd)

  IsCommAlgebraHom : {A B : Type ℓ'}
    (M : CommAlgebraStr R A) (f : A → B) (N : CommAlgebraStr R B)
    → Type (ℓ-max ℓ ℓ')
  IsCommAlgebraHom M f N =
    IsAlgebraHom (CommAlgebraStr→AlgebraStr M) f (CommAlgebraStr→AlgebraStr N)

  CommAlgebraHom : (M N : CommAlgebra R ℓ') → Type (ℓ-max ℓ ℓ')
  CommAlgebraHom M N = Σ[ f ∈ (⟨ M ⟩ → ⟨ N ⟩) ] IsCommAlgebraHom (M .snd) f (N .snd)

isPropIsCommAlgebra : (R : CommRing ℓ) {A : Type ℓ'}
  (0a 1a : A)
  (_+_ _·_ : A → A → A)
  (-_ : A → A)
  (_⋆_ : ⟨ R ⟩ → A → A)
  → isProp (IsCommAlgebra R 0a 1a _+_ _·_ -_ _⋆_)
isPropIsCommAlgebra R _ _ _ _ _ _ =
  isOfHLevelRetractFromIso 1 IsCommAlgebraIsoΣ
    (isPropΣ (isPropIsAlgebra _ _ _ _ _ _ _)
      (λ alg → isPropΠ2 λ _ _ → alg .IsAlgebra.is-set _ _))

𝒮ᴰ-CommAlgebra : (R : CommRing ℓ) → DUARel (𝒮-Univ ℓ') (CommAlgebraStr R) (ℓ-max ℓ ℓ')
𝒮ᴰ-CommAlgebra R =
  𝒮ᴰ-Record (𝒮-Univ _) (IsCommAlgebraEquiv {R = R})
    (fields:
      data[ 0a ∣ nul ∣ pres0 ]
      data[ 1a ∣ nul ∣ pres1 ]
      data[ _+_ ∣ bin ∣ pres+ ]
      data[ _·_ ∣ bin ∣ pres· ]
      data[ -_ ∣ autoDUARel _ _ ∣ pres- ]
      data[ _⋆_ ∣ autoDUARel _ _ ∣ pres⋆ ]
      prop[ isCommAlgebra ∣ (λ _ _ → isPropIsCommAlgebra _ _ _ _ _ _ _) ])
  where
  open CommAlgebraStr
  open IsAlgebraHom

  -- faster with some sharing
  nul = autoDUARel (𝒮-Univ _) (λ A → A)
  bin = autoDUARel (𝒮-Univ _) (λ A → A → A → A)

CommAlgebraPath : (R : CommRing ℓ) → (A B : CommAlgebra R ℓ') → (CommAlgebraEquiv A B) ≃ (A ≡ B)
CommAlgebraPath R = ∫ (𝒮ᴰ-CommAlgebra R) .UARel.ua

isGroupoidCommAlgebra : {R : CommRing ℓ} → isGroupoid (CommAlgebra R ℓ')
isGroupoidCommAlgebra A B = isOfHLevelRespectEquiv 2 (CommAlgebraPath _ _ _) (isSetAlgebraEquiv _ _)

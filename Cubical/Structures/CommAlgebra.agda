{-# OPTIONS --cubical --safe #-}

module Cubical.Structures.CommAlgebra where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.SIP

open import Cubical.Data.Sigma

open import Cubical.Structures.CommRing renaming (⟨_⟩ to ⟨_⟩r)
open import Cubical.Structures.Algebra  hiding (⟨_⟩)

private
  variable
    ℓ ℓ′ : Level

record IsCommAlgebra (R : CommRing {ℓ}) {A : Type ℓ}
                     (0a : A) (1a : A)
                     (_+_ : A → A → A) (_·_ : A → A → A) (-_ : A → A)
                     (_⋆_ : ⟨ R ⟩r → A → A) : Type ℓ where

  constructor iscommalgebra

  field
    isAlgebra : IsAlgebra (CommRing→Ring R) 0a 1a _+_ _·_ -_ _⋆_
    comm      : (x y : A) → x · y ≡ y · x

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
    _⋆_            : ⟨ R ⟩r → Carrier → Carrier
    isCommAlgebra  : IsCommAlgebra R 0a 1a _+_ _·_ -_ _⋆_

module _ (R : CommRing {ℓ}) where
  open CommRing R using (1r) renaming (_+_ to _+r_; _·_ to _·s_)

  makeIsCommAlgebra : {A : Type ℓ} {0a 1a : A}
                      {_+_ _·_ : A → A → A} { -_ : A → A} {_⋆_ : ⟨ R ⟩r → A → A}
                      (isSet-A : isSet A)
                      (+-assoc :  (x y z : A) → x + (y + z) ≡ (x + y) + z)
                      (+-rid : (x : A) → x + 0a ≡ x)
                      (+-rinv : (x : A) → x + (- x) ≡ 0a)
                      (+-comm : (x y : A) → x + y ≡ y + x)
                      (·-assoc :  (x y z : A) → x · (y · z) ≡ (x · y) · z)
                      (·-lid : (x : A) → 1a · x ≡ x)
                      (·-ldist-+ : (x y z : A) → (x + y) · z ≡ (x · z) + (y · z))
                      (·-comm : (x y : A) → x · y ≡ y · x)
                      (⋆-assoc : (r s : ⟨ R ⟩r) (x : A) → (r ·s s) ⋆ x ≡ r ⋆ (s ⋆ x))
                      (⋆-ldist : (r s : ⟨ R ⟩r) (x : A) → (r +r s) ⋆ x ≡ (r ⋆ x) + (s ⋆ x))
                      (⋆-rdist : (r : ⟨ R ⟩r) (x y : A) → r ⋆ (x + y) ≡ (r ⋆ x) + (r ⋆ y))
                      (⋆-lid   : (x : A) → 1r ⋆ x ≡ x)
                      (⋆-lassoc : (r : ⟨ R ⟩r) (x y : A) → (r ⋆ x) · y ≡ r ⋆ (x · y))
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


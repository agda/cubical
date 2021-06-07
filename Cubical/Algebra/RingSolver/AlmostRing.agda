{-# OPTIONS --safe #-}
module Cubical.Algebra.RingSolver.AlmostRing where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ)

open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.AbGroup

private
  variable
    ℓ : Level

record IsAlmostRing {R : Type ℓ}
                  (0r 1r : R) (_+_ _·_ : R → R → R) (-_ : R → R) : Type ℓ where

  constructor isalmostring

  field
    +IsMonoid : IsMonoid 0r _+_
    ·IsMonoid : IsMonoid 1r _·_
    +Comm : (x y : R) → x + y ≡ y + x
    ·Comm : (x y : R) → x · y ≡ y · x
    ·DistR+ : (x y z : R) → x · (y + z) ≡ (x · y) + (x · z)
    ·DistL+ :  (x y z : R) → (x + y) · z ≡ (x · z) + (y · z)
    -Comm· : (x y : R) → - (x · y) ≡ (- x) · y
    -Dist+ : (x y : R) → - (x + y) ≡ (- x) + (- y)
    0LeftAnnihilates : (x : R) → 0r · x ≡ 0r
    0RightAnnihilates : (x : R) → x · 0r ≡ 0r

  open IsMonoid +IsMonoid public
    renaming
      ( assoc       to +Assoc
      ; identity    to +Identity
      ; lid         to +Lid
      ; rid         to +Rid
      ; isSemigroup to +IsSemigroup)

  open IsMonoid ·IsMonoid public
    renaming
      ( assoc       to ·Assoc
      ; identity    to ·Identity
      ; lid         to ·Lid
      ; rid         to ·Rid
      ; isSemigroup to ·IsSemigroup )
    hiding
      ( is-set ) -- We only want to export one proof of this

record AlmostRing ℓ : Type (ℓ-suc ℓ) where

  constructor almostring

  field
    Carrier : Type ℓ
    0r      : Carrier
    1r      : Carrier
    _+_     : Carrier → Carrier → Carrier
    _·_     : Carrier → Carrier → Carrier
    -_      : Carrier → Carrier
    isAlmostRing  : IsAlmostRing 0r 1r _+_ _·_ -_

  infixl 9 _^_
  infixl 8 _·_
  infixl 7 -_
  infixl 6 _+_
  infixl 6 _-_

  open IsAlmostRing isAlmostRing public

  _^_ : Carrier → ℕ → Carrier
  x ^ 0 = 1r
  x ^ ℕ.suc k = x · (x ^ k)

  _-_ : Carrier → Carrier → Carrier
  x - y = x + (- y)

-- Extractor for the carrier type
⟨_⟩ : AlmostRing ℓ → Type ℓ
⟨_⟩ = AlmostRing.Carrier

isSetAlmostRing : (R : AlmostRing ℓ) → isSet ⟨ R ⟩
isSetAlmostRing R = R .AlmostRing.isAlmostRing .IsAlmostRing.·IsMonoid .IsMonoid.isSemigroup .IsSemigroup.is-set

module Theory (R : AlmostRing ℓ) where
  open AlmostRing R

  0IsSelfinverse : - 0r ≡ 0r
  0IsSelfinverse = - 0r          ≡⟨ cong -_ (sym (·Lid 0r))  ⟩
                   - (1r · 0r)   ≡⟨ -Comm· 1r 0r ⟩
                   (- 1r) · 0r   ≡⟨ 0RightAnnihilates (- 1r) ⟩
                   0r ∎

  ·CommRight : (x y z : ⟨ R ⟩)
               → x · y · z ≡ x · z · y
  ·CommRight x y z = x · y · z   ≡⟨ sym (·Assoc _ _ _) ⟩
                     x · (y · z) ≡⟨ cong (λ u → x · u) (·Comm _ _) ⟩
                     x · (z · y) ≡⟨ ·Assoc _ _ _ ⟩
                     x · z · y ∎

  +ShufflePairs : (a b c d : ⟨ R ⟩)
                → (a + b) + (c + d) ≡ (a + c) + (b + d)
  +ShufflePairs a b c d =
    (a + b) + (c + d) ≡⟨ +Assoc _ _ _ ⟩
    ((a + b) + c) + d ≡⟨ cong (λ u → u + d) (sym (+Assoc _ _ _)) ⟩
    (a + (b + c)) + d ≡⟨ cong (λ u → (a + u) + d) (+Comm _ _) ⟩
    (a + (c + b)) + d ≡⟨ cong (λ u → u + d) (+Assoc _ _ _) ⟩
    ((a + c) + b) + d ≡⟨ sym (+Assoc _ _ _) ⟩
    (a + c) + (b + d) ∎

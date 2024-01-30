{-

ℚ is a Field

-}
{-# OPTIONS --safe #-}
module Cubical.Algebra.Field.Instances.Rationals where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Int.MoreInts.QuoInt
  using    (ℤ ; spos ; sneg ; pos ; neg ; signed ; posneg ; isSetℤ ; 0≢1-ℤ)
  renaming (_·_ to _·ℤ_ ; -_ to -ℤ_
           ; ·-zeroˡ to ·ℤ-zeroˡ
           ; ·-identityʳ to ·ℤ-identityʳ)
open import Cubical.HITs.SetQuotients as SetQuot
open import Cubical.Data.Rationals.MoreRationals.QuoQ
  using    (ℚ ; ℕ₊₁→ℤ ; isEquivRel∼)

open import Cubical.Algebra.Field
open import Cubical.Algebra.CommRing
open import Cubical.Tactics.CommRingSolver
open import Cubical.Algebra.CommRing.Instances.QuoInt
open import Cubical.Algebra.CommRing.Instances.Rationals

open import Cubical.Relation.Nullary


-- It seems there are bugs when applying ring solver to explicit ring.
-- The following is a work-around.
private
  module Helpers {ℓ : Level}(𝓡 : CommRing ℓ) where
    open CommRingStr (𝓡 .snd)

    helper1 : (x y : 𝓡 .fst) → (x · y) · 1r ≡ 1r · (y · x)
    helper1 _ _ = solve! 𝓡

    helper2 : (x y : 𝓡 .fst) → ((- x) · (- y)) · 1r ≡ 1r · (y · x)
    helper2 _ _ = solve! 𝓡


-- A rational number is zero if and only if its numerator is zero

a/b≡0→a≡0 : (x : ℤ × ℕ₊₁) → [ x ] ≡ 0 → x .fst ≡ 0
a/b≡0→a≡0 (a , b) a/b≡0 = sym (·ℤ-identityʳ a) ∙ a·1≡0·b ∙ ·ℤ-zeroˡ (ℕ₊₁→ℤ b)
  where a·1≡0·b : a ·ℤ 1 ≡ 0 ·ℤ (ℕ₊₁→ℤ b)
        a·1≡0·b = effective (λ _ _ → isSetℤ _ _) isEquivRel∼ _ _ a/b≡0

a≡0→a/b≡0 : (x : ℤ × ℕ₊₁) → x .fst ≡ 0 → [ x ] ≡ 0
a≡0→a/b≡0 (a , b) a≡0 = eq/ _ _ a·1≡0·b
  where a·1≡0·b : a ·ℤ 1 ≡ 0 ·ℤ (ℕ₊₁→ℤ b)
        a·1≡0·b = (λ i → a≡0 i ·ℤ 1) ∙ ·ℤ-zeroˡ {s = spos} 1 ∙ sym (·ℤ-zeroˡ (ℕ₊₁→ℤ b))


-- ℚ is a field

open CommRingStr (ℚCommRing .snd)
open Units        ℚCommRing
open Helpers      ℤCommRing


hasInverseℚ : (q : ℚ) → ¬ q ≡ 0 → Σ[ p ∈ ℚ ] q · p ≡ 1
hasInverseℚ = SetQuot.elimProp (λ q → isPropΠ (λ _ → inverseUniqueness q))
  (λ x x≢0 → let a≢0 = λ a≡0 → x≢0 (a≡0→a/b≡0 x a≡0) in inv-helper x a≢0 , inv·-helper x a≢0)
  where
  inv-helper : (x : ℤ × ℕ₊₁) → ¬ x .fst ≡ 0 → ℚ
  inv-helper (signed spos (suc a) , b) _ = [ ℕ₊₁→ℤ b , 1+ a ]
  inv-helper (signed sneg (suc a) , b) _ = [ -ℤ ℕ₊₁→ℤ b , 1+ a ]
  inv-helper (signed spos zero , _) a≢0 = Empty.rec (a≢0 refl)
  inv-helper (signed sneg zero , _) a≢0 = Empty.rec (a≢0 (sym posneg))
  inv-helper (posneg i , _) a≢0 = Empty.rec (a≢0 (λ j → posneg (i ∧ ~ j)))

  inv·-helper : (x : ℤ × ℕ₊₁)(a≢0 : ¬ x .fst ≡ 0) → [ x ] · inv-helper x a≢0 ≡ 1
  inv·-helper (signed spos zero , b) a≢0 = Empty.rec (a≢0 refl)
  inv·-helper (signed sneg zero , b) a≢0 = Empty.rec (a≢0 (sym posneg))
  inv·-helper (posneg i , b) a≢0 = Empty.rec (a≢0 (λ j → posneg (i ∧ ~ j)))
  inv·-helper (signed spos (suc a) , b) _ = eq/ _ _ (helper1 (pos (suc a)) (ℕ₊₁→ℤ b))
  inv·-helper (signed sneg (suc a) , b) _ = eq/ _ _ (helper2 (pos (suc a)) (ℕ₊₁→ℤ b))

0≢1-ℚ : ¬ Path ℚ 0 1
0≢1-ℚ p = 0≢1-ℤ (effective (λ _ _ → isSetℤ _ _) isEquivRel∼ _ _ p)


-- The instance

ℚField : Field ℓ-zero
ℚField = makeFieldFromCommRing ℚCommRing hasInverseℚ 0≢1-ℚ

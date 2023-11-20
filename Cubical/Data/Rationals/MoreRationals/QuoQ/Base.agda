{-# OPTIONS --safe #-}
module Cubical.Data.Rationals.MoreRationals.QuoQ.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.Data.Nat as ℕ using (discreteℕ)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Sigma
open import Cubical.Data.Int.MoreInts.QuoInt

open import Cubical.HITs.SetQuotients as SetQuotient
  using ([_]; eq/; discreteSetQuotients) renaming (_/_ to _//_) public

open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary.Base
open BinaryRelation

ℕ₊₁→ℤ : ℕ₊₁ → ℤ
ℕ₊₁→ℤ n = pos (ℕ₊₁→ℕ n)

private
  ℕ₊₁→ℤ-hom : ∀ m n → ℕ₊₁→ℤ (m ·₊₁ n) ≡ ℕ₊₁→ℤ m · ℕ₊₁→ℤ n
  ℕ₊₁→ℤ-hom _ _ = refl


-- ℚ as a set quotient of ℤ × ℕ₊₁ (as in the HoTT book)

_∼_ : ℤ × ℕ₊₁ → ℤ × ℕ₊₁ → Type₀
(a , b) ∼ (c , d) = a · ℕ₊₁→ℤ d ≡ c · ℕ₊₁→ℤ b

ℚ : Type₀
ℚ = (ℤ × ℕ₊₁) // _∼_


isSetℚ : isSet ℚ
isSetℚ = SetQuotient.squash/

[_/_] : ℤ → ℕ₊₁ → ℚ
[ a / b ] = [ a , b ]


isEquivRel∼ : isEquivRel _∼_
isEquivRel.reflexive isEquivRel∼ (a , b) = refl
isEquivRel.symmetric isEquivRel∼ (a , b) (c , d) = sym
isEquivRel.transitive isEquivRel∼ (a , b) (c , d) (e , f) p q = ·-injʳ _ _ _ r
  where r = (a · ℕ₊₁→ℤ f) · ℕ₊₁→ℤ d ≡[ i ]⟨ ·-comm a (ℕ₊₁→ℤ f) i · ℕ₊₁→ℤ d ⟩
            (ℕ₊₁→ℤ f · a) · ℕ₊₁→ℤ d ≡⟨ sym (·-assoc (ℕ₊₁→ℤ f) a (ℕ₊₁→ℤ d)) ⟩
            ℕ₊₁→ℤ f · (a · ℕ₊₁→ℤ d) ≡[ i ]⟨ ℕ₊₁→ℤ f · p i ⟩
            ℕ₊₁→ℤ f · (c · ℕ₊₁→ℤ b) ≡⟨ ·-assoc (ℕ₊₁→ℤ f) c (ℕ₊₁→ℤ b) ⟩
            (ℕ₊₁→ℤ f · c) · ℕ₊₁→ℤ b ≡[ i ]⟨ ·-comm (ℕ₊₁→ℤ f) c i · ℕ₊₁→ℤ b ⟩
            (c · ℕ₊₁→ℤ f) · ℕ₊₁→ℤ b ≡[ i ]⟨ q i · ℕ₊₁→ℤ b ⟩
            (e · ℕ₊₁→ℤ d) · ℕ₊₁→ℤ b ≡⟨ sym (·-assoc e (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b)) ⟩
            e · (ℕ₊₁→ℤ d · ℕ₊₁→ℤ b) ≡[ i ]⟨ e · ·-comm (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b) i ⟩
            e · (ℕ₊₁→ℤ b · ℕ₊₁→ℤ d) ≡⟨ ·-assoc e (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ d) ⟩
            (e · ℕ₊₁→ℤ b) · ℕ₊₁→ℤ d ∎

eq/⁻¹ : ∀ x y → Path ℚ [ x ] [ y ] → x ∼ y
eq/⁻¹ = SetQuotient.effective (λ _ _ → isSetℤ _ _) isEquivRel∼

discreteℚ : Discrete ℚ
discreteℚ = discreteSetQuotients isEquivRel∼ (λ _ _ → discreteℤ _ _)


-- Natural number and negative integer literals for ℚ

open import Cubical.Data.Nat.Literals public

instance
  fromNatℚ : HasFromNat ℚ
  fromNatℚ = record { Constraint = λ _ → Unit ; fromNat = λ n → [ pos n / 1 ] }

instance
  fromNegℚ : HasFromNeg ℚ
  fromNegℚ = record { Constraint = λ _ → Unit ; fromNeg = λ n → [ neg n / 1 ] }

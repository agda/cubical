{-# OPTIONS --safe #-}
module Cubical.Data.Rationals.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function

open import Cubical.Data.Nat as ℕ using (discreteℕ)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Sigma
open import Cubical.Data.Int

open import Cubical.HITs.SetQuotients as SetQuotient
  using ([_]; eq/; discreteSetQuotients) renaming (_/_ to _//_) public

open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary.Base
open BinaryRelation

ℕ₊₁→ℤ : ℕ₊₁ → ℤ
ℕ₊₁→ℤ n = pos (ℕ₊₁→ℕ n)


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
isEquivRel.transitive isEquivRel∼ (a , b) (c , d) (e , f) p q = ·rCancel _ _ (e · pos (ℕ.suc (ℕ₊₁.n b))) r (ℕ.snotz ∘ injPos)
  where r = (a · ℕ₊₁→ℤ f) · ℕ₊₁→ℤ d ≡[ i ]⟨ ·Comm a (ℕ₊₁→ℤ f) i · ℕ₊₁→ℤ d ⟩
            (ℕ₊₁→ℤ f · a) · ℕ₊₁→ℤ d ≡⟨ sym (·Assoc (ℕ₊₁→ℤ f) a (ℕ₊₁→ℤ d)) ⟩
            ℕ₊₁→ℤ f · (a · ℕ₊₁→ℤ d) ≡[ i ]⟨ ℕ₊₁→ℤ f · p i ⟩
            ℕ₊₁→ℤ f · (c · ℕ₊₁→ℤ b) ≡⟨ ·Assoc (ℕ₊₁→ℤ f) c (ℕ₊₁→ℤ b) ⟩
            (ℕ₊₁→ℤ f · c) · ℕ₊₁→ℤ b ≡[ i ]⟨ ·Comm (ℕ₊₁→ℤ f) c i · ℕ₊₁→ℤ b ⟩
            (c · ℕ₊₁→ℤ f) · ℕ₊₁→ℤ b ≡[ i ]⟨ q i · ℕ₊₁→ℤ b ⟩
            (e · ℕ₊₁→ℤ d) · ℕ₊₁→ℤ b ≡⟨ sym (·Assoc e (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b)) ⟩
            e · (ℕ₊₁→ℤ d · ℕ₊₁→ℤ b) ≡[ i ]⟨ e · ·Comm (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b) i ⟩
            e · (ℕ₊₁→ℤ b · ℕ₊₁→ℤ d) ≡⟨ ·Assoc e (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ d) ⟩
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

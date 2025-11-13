module Cubical.Relation.Binary.Order.Pseudolattice.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Binary.Order.Poset renaming (isPseudolattice to pseudolattice)

open import Cubical.Relation.Binary.Order.Pseudolattice.Base

open import Cubical.Algebra.Semigroup

open BinaryRelation

private
  variable
    ℓ ℓ' : Level

DualPseudolattice : Pseudolattice ℓ ℓ' → Pseudolattice ℓ ℓ'
DualPseudolattice L .fst = L .fst
DualPseudolattice L .snd .PseudolatticeStr._≤_ = Dual (L .snd .PseudolatticeStr._≤_)
DualPseudolattice L .snd .PseudolatticeStr.is-pseudolattice = isPL
  where
    open module L≤ = PseudolatticeStr (L .snd)
    open IsPseudolattice
    isPL : IsPseudolattice _
    isPL .isPoset              = isPosetDual L≤.isPoset
    isPL .isPseudolattice .fst = L≤.isPseudolattice .snd
    isPL .isPseudolattice .snd = L≤.isPseudolattice .fst

module MeetProperties (L≤ : Pseudolattice ℓ ℓ') where
  private
    L = L≤ .fst
    open PseudolatticeStr (L≤ .snd)
    variable
      a b c x : L

  isMeet∧ : ∀ {a b x} → x ≤ (a ∧l b) ≃ (x ≤ a) × (x ≤ b)
  isMeet∧ {a} {b} {x} = isPseudolattice .fst a b .snd x

  ∧≤L : (a ∧l b) ≤ a
  ∧≤L = equivFun isMeet∧ (is-refl _) .fst

  ∧≤R : (a ∧l b) ≤ b
  ∧≤R = equivFun isMeet∧ (is-refl _) .snd

  ∧GLB : ∀ {a b x} → x ≤ a → x ≤ b → x ≤ a ∧l b
  ∧GLB = curry (invEq isMeet∧)

  isMeet→≡∧ : ∀ m
              → (∀ {x} → x ≤ m → x ≤ a)
              → (∀ {x} → x ≤ m → x ≤ b)
              → (∀ {x} → x ≤ a → x ≤ b → x ≤ m)
              → a ∧l b ≡ m
  isMeet→≡∧ {a = a} {b = b} m l r u =
    fst $ PathPΣ $ MeetUnique isPoset a b (isPseudolattice .fst a b) $
    m , λ x → propBiimpl→Equiv (is-prop-valued _ _)
                               (isProp× (is-prop-valued _ _) (is-prop-valued _ _))
    (λ x≤m → l x≤m , r x≤m)
    (uncurry u)

  ∧Idem : a ∧l a ≡ a
  ∧Idem = meetIdemp isPoset (isPseudolattice .fst) _

  ∧Comm : a ∧l b ≡ b ∧l a
  ∧Comm = meetComm isPoset (isPseudolattice .fst) _ _

  ∧Assoc : a ∧l (b ∧l c) ≡ (a ∧l b) ∧l c
  ∧Assoc = meetAssoc isPoset (isPseudolattice .fst) _ _ _

  ≤≃∧ : (a ≤ b) ≃ (a ≡ a ∧l b)
  ≤≃∧ = order≃meet isPoset _ _ _ λ _ → isMeet∧

  ≤→∧ : a ≤ b → a ≡ a ∧l b
  ≤→∧ = equivFun ≤≃∧

  ≤→∧≡Left : a ≤ b → a ∧l b ≡ a
  ≤→∧≡Left = sym ∘ ≤→∧

  ≥→∧≡Right : b ≤ a → a ∧l b ≡ b
  ≥→∧≡Right = sym ∘ (_∙ ∧Comm) ∘ ≤→∧

  Pseudolattice→Semigroup∧ : Semigroup ℓ
  Pseudolattice→Semigroup∧ .fst = L
  Pseudolattice→Semigroup∧ .snd .SemigroupStr._·_ = _∧l_
  Pseudolattice→Semigroup∧ .snd .SemigroupStr.isSemigroup =
    issemigroup is-set (λ _ _ _ → ∧Assoc)

open MeetProperties public

module _ (L≤ : Pseudolattice ℓ ℓ') where
  open MeetProperties (DualPseudolattice L≤) public renaming (
      isMeet∧ to isJoin∨ ; ∧≤L to L≤∨ ; ∧≤R to R≤∨ ; isMeet→≡∧ to isJoin→≡∨
    ; ∧Comm to ∨Comm ; ∧Idem to ∨Idem ; ∧Assoc to ∨Assoc
    ; ≤≃∧ to ≤≃∨ ; ≤→∧ to ≤→∨ ; ≤→∧≡Left to ≥→∨≡Left ; ≥→∧≡Right to ≤→∨≡Right
    ; ∧GLB to ∨LUB ; Pseudolattice→Semigroup∧ to Pseudolattice→Semigroup∨)

module Cubical.Relation.Binary.Order.Pseudolattice.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Binary.Order.Proset
open import Cubical.Relation.Binary.Order.Poset renaming (isPseudolattice to pseudolattice)
open import Cubical.Relation.Binary.Order.Quoset

open import Cubical.Relation.Binary.Order.Pseudolattice.Base

open import Cubical.Relation.Nullary

open import Cubical.Algebra.Semigroup

private
  variable
    ℓ ℓ' ℓ'' : Level

module _
  {A : Type ℓ}
  {R : Rel A A ℓ'}
  where

  open BinaryRelation
  open IsPseudolattice

  isPseudolattice→isPoset : IsPseudolattice R → IsPoset R
  isPseudolattice→isPoset = isPoset

  isPseudolattice→isProset : IsPseudolattice R → IsProset R
  isPseudolattice→isProset = isPoset→isProset ∘ isPoset

  isPseudolatticeDecidable→Discrete : IsPseudolattice R → isDecidable R → Discrete A
  isPseudolatticeDecidable→Discrete = isPosetDecidable→Discrete ∘ isPoset

  isPseudolattice→isQuosetIrreflKernel : IsPseudolattice R → IsQuoset (IrreflKernel R)
  isPseudolattice→isQuosetIrreflKernel = isPoset→isQuosetIrreflKernel ∘ isPoset

  isPseudolatticeDecidable→isQuosetDecidable : IsPseudolattice R → isDecidable R → isDecidable (IrreflKernel R)
  isPseudolatticeDecidable→isQuosetDecidable = isPosetDecidable→isQuosetDecidable ∘ isPoset

  isPseudolatticeDual : IsPseudolattice R → IsPseudolattice (Dual R)
  isPseudolatticeDual pl .isPoset = isPosetDual (isPoset pl)
  isPseudolatticeDual pl .isPseudolattice .fst = pl .isPseudolattice .snd
  isPseudolatticeDual pl .isPseudolattice .snd = pl .isPseudolattice .fst

Pseudolattice→Proset : Pseudolattice ℓ ℓ' → Proset ℓ ℓ'
Pseudolattice→Proset (_ , pl) = proset _ _ (isPoset→isProset isPoset)
  where open PseudolatticeStr pl

Pseudolattice→Poset : Pseudolattice ℓ ℓ' → Poset ℓ ℓ'
Pseudolattice→Poset (_ , pl) = poset _ _ isPoset
  where open PseudolatticeStr pl

Pseudolattice→Quoset : Pseudolattice ℓ ℓ' → Quoset ℓ (ℓ-max ℓ ℓ')
Pseudolattice→Quoset (_ , pl) = quoset _ _ (isPoset→isQuosetIrreflKernel isPoset)
  where open PseudolatticeStr pl

DualPseudolattice : Pseudolattice ℓ ℓ' → Pseudolattice ℓ ℓ'
DualPseudolattice (_ , pl) = _ , pseudolatticestr _ (isPseudolatticeDual is-pseudolattice)
  where open PseudolatticeStr pl

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

module JoinProperties (L≤ : Pseudolattice ℓ ℓ') where
  open MeetProperties (DualPseudolattice L≤) public renaming (
      isMeet∧ to isJoin∨ ; ∧≤L to L≤∨ ; ∧≤R to R≤∨ ; isMeet→≡∧ to isJoin→≡∨
    ; ∧Comm to ∨Comm ; ∧Idem to ∨Idem ; ∧Assoc to ∨Assoc
    ; ≤≃∧ to ≤≃∨ ; ≤→∧ to ≤→∨ ; ≤→∧≡Left to ≥→∨≡Left ; ≥→∧≡Right to ≤→∨≡Right
    ; ∧GLB to ∨LUB ; Pseudolattice→Semigroup∧ to Pseudolattice→Semigroup∨)

open JoinProperties public

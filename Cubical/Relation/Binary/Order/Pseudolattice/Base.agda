module Cubical.Relation.Binary.Order.Pseudolattice.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.SIP

open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Binary.Order.Poset renaming (isPseudolattice to pseudolattice)
open import Cubical.Relation.Binary.Order.StrictOrder

open BinaryRelation

private
  variable
    ℓ ℓ' : Level

record IsPseudolattice {L : Type ℓ} (_≤_ : L → L → Type ℓ') : Type (ℓ-max ℓ ℓ') where
  constructor ispseudolattice

  field
    isPoset : IsPoset _≤_
    isPseudolattice : pseudolattice (poset L _≤_ isPoset)

  open IsPoset isPoset public

  _∧l_ : L → L → L
  a ∧l b = (isPseudolattice .fst a b) .fst

  _∨l_ : L → L → L
  a ∨l b = (isPseudolattice .snd a b) .fst

  infixl 7 _∧l_
  infixl 6 _∨l_

record PseudolatticeStr (ℓ' : Level) (L : Type ℓ) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  constructor pseudolatticestr

  field
    _≤_ : L → L → Type ℓ'
    is-pseudolattice : IsPseudolattice _≤_

  infix 5 _≤_

  open IsPseudolattice is-pseudolattice public

Pseudolattice : ∀ ℓ ℓ' → Type (ℓ-suc (ℓ-max ℓ ℓ'))
Pseudolattice ℓ ℓ' = TypeWithStr ℓ (PseudolatticeStr ℓ')

makeIsPseudolattice : {L : Type ℓ} {_≤_ : L → L → Type ℓ'}
                      (is-setL : isSet L)
                      (is-prop-valued : isPropValued _≤_)
                      (is-refl : isRefl _≤_)
                      (is-trans : isTrans _≤_)
                      (is-antisym : isAntisym _≤_)
                      (is-meet-semipseudolattice : isMeetSemipseudolattice (poset L _≤_ (isposet is-setL is-prop-valued is-refl is-trans is-antisym)))
                      (is-join-semipseudolattice : isJoinSemipseudolattice (poset L _≤_ (isposet is-setL is-prop-valued is-refl is-trans is-antisym)))
                      → IsPseudolattice _≤_
makeIsPseudolattice {_≤_ = _≤_} is-setL is-prop-valued is-refl is-trans is-antisym is-meet-semipseudolattice is-join-semipseudolattice = PS
  where
    PS : IsPseudolattice _≤_
    PS .IsPseudolattice.isPoset = isposet is-setL is-prop-valued is-refl is-trans is-antisym
    PS .IsPseudolattice.isPseudolattice = is-meet-semipseudolattice , is-join-semipseudolattice

module _
  (P : Poset ℓ ℓ') (_∧_ _∨_ : ⟨ P ⟩ → ⟨ P ⟩ → ⟨ P ⟩) where
  open PosetStr (str P) renaming (_≤_ to infix 8 _≤_)
  module _
    (π₁ : ∀ {a b}   → a ∧ b ≤ a)
    (π₂ : ∀ {a b}   → a ∧ b ≤ b)
    (ϕ  : ∀ {a b x} → x ≤ a → x ≤ b → x ≤ a ∧ b)
    (ι₁ : ∀ {a b}   → a ≤ a ∨ b)
    (ι₂ : ∀ {a b}   → b ≤ a ∨ b)
    (ψ  : ∀ {a b x} → a ≤ x → b ≤ x → a ∨ b ≤ x) where

    makePseudolatticeFromPoset : Pseudolattice ℓ ℓ'
    makePseudolatticeFromPoset .fst = ⟨ P ⟩
    makePseudolatticeFromPoset .snd .PseudolatticeStr._≤_ = (str P) .PosetStr._≤_
    makePseudolatticeFromPoset .snd .PseudolatticeStr.is-pseudolattice = isPL where
      isPL : IsPseudolattice _≤_
      isPL .IsPseudolattice.isPoset = isPoset
      isPL .IsPseudolattice.isPseudolattice .fst a b .fst = a ∧ b
      isPL .IsPseudolattice.isPseudolattice .fst a b .snd x = propBiimpl→Equiv
        (is-prop-valued _ _)
        (isProp× (is-prop-valued _ _) (is-prop-valued _ _))
        (λ x≤a∧b → is-trans _ _ _ x≤a∧b π₁ , is-trans _ _ _ x≤a∧b π₂)
        (uncurry ϕ)
      isPL .IsPseudolattice.isPseudolattice .snd a b .fst = a ∨ b
      isPL .IsPseudolattice.isPseudolattice .snd a b .snd x = propBiimpl→Equiv
        (is-prop-valued _ _)
        (isProp× (is-prop-valued _ _) (is-prop-valued _ _))
        (λ a∨b≤x → is-trans _ _ _ ι₁ a∨b≤x , is-trans _ _ _ ι₂ a∨b≤x)
        (uncurry ψ)

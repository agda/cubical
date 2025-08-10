module Cubical.Relation.Binary.Order.Pseudolattice.Base where

open import Cubical.Foundations.Prelude
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

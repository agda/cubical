module Cubical.Relation.Binary.Order.Pseudolattice.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.SIP

open import Cubical.Reflection.RecordEquiv
open import Cubical.Reflection.StrictEquiv

open import Cubical.Displayed.Base
open import Cubical.Displayed.Auto
open import Cubical.Displayed.Record
open import Cubical.Displayed.Universe

open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Binary.Order.Poset renaming (
  isPseudolattice to pseudolattice ;
  isPropIsPseudolattice to is-prop-is-pseudolattice)

open BinaryRelation

private
  variable
    ℓ ℓ' ℓ₀ ℓ₀' ℓ₁ ℓ₁' : Level

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


unquoteDecl IsPseudolatticeIsoΣ = declareRecordIsoΣ IsPseudolatticeIsoΣ (quote IsPseudolattice)

record PseudolatticeStr (ℓ' : Level) (L : Type ℓ) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  constructor pseudolatticestr

  field
    _≤_ : L → L → Type ℓ'
    is-pseudolattice : IsPseudolattice _≤_

  infix 5 _≤_

  open IsPseudolattice is-pseudolattice public


unquoteDecl PseudolatticeStrIsoΣ = declareRecordIsoΣ PseudolatticeStrIsoΣ (quote PseudolatticeStr)

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


record IsPseudolatticeEquiv {A : Type ℓ₀} {B : Type ℓ₁}
  (M : PseudolatticeStr ℓ₀' A) (e : A ≃ B) (N : PseudolatticeStr ℓ₁' B)
  : Type (ℓ-max (ℓ-max ℓ₀ ℓ₀') ℓ₁')
  where
  constructor
   ispseudolatticeequiv
  -- Shorter qualified names
  private
    module M = PseudolatticeStr M
    module N = PseudolatticeStr N

  field
    pres≤ : (x y : A) → x M.≤ y ≃ equivFun e x N.≤ equivFun e y


PseudolatticeEquiv : (M : Pseudolattice ℓ₀ ℓ₀') (N : Pseudolattice ℓ₁ ℓ₁')
                     → Type (ℓ-max (ℓ-max ℓ₀ ℓ₀') (ℓ-max ℓ₁ ℓ₁'))
PseudolatticeEquiv M N = Σ[ e ∈ ⟨ M ⟩ ≃ ⟨ N ⟩ ] IsPseudolatticeEquiv (M .snd) e (N .snd)

isPropIsPseudolattice : {L : Type ℓ} (_≤_ : L → L → Type ℓ') → isProp (IsPseudolattice _≤_)
isPropIsPseudolattice {L = L} _≤_ = isOfHLevelRetractFromIso 1
  IsPseudolatticeIsoΣ $ isPropΣ
  (isPropIsPoset _≤_) λ isPoset →
  is-prop-is-pseudolattice (poset L _≤_ isPoset)

𝒮ᴰ-Pseudolattice : DUARel (𝒮-Univ ℓ) (PseudolatticeStr ℓ') (ℓ-max ℓ ℓ')
𝒮ᴰ-Pseudolattice =
  𝒮ᴰ-Record (𝒮-Univ _) IsPseudolatticeEquiv
    (fields:
      data[ _≤_ ∣ autoDUARel _ _ ∣ pres≤ ]
      prop[ is-pseudolattice ∣ (λ _ _ → isPropIsPseudolattice _) ])
    where
    open PseudolatticeStr
    open IsPseudolattice
    open IsPseudolatticeEquiv

PseudolatticePath : (M N : Pseudolattice ℓ ℓ') → PseudolatticeEquiv M N ≃ (M ≡ N)
PseudolatticePath = ∫ 𝒮ᴰ-Pseudolattice .UARel.ua

-- an easier way of establishing an equivalence of pseudolattices
module _ {P : Pseudolattice ℓ₀ ℓ₀'} {S : Pseudolattice ℓ₁ ℓ₁'} (e : ⟨ P ⟩ ≃ ⟨ S ⟩) where
  private
    module P = PseudolatticeStr (P .snd)
    module S = PseudolatticeStr (S .snd)

  module _ (isMon : ∀ x y → x P.≤ y → equivFun e x S.≤ equivFun e y)
           (isMonInv : ∀ x y → x S.≤ y → invEq e x P.≤ invEq e y) where
    open IsPseudolatticeEquiv
    open IsPseudolattice

    makeIsPseudolatticeEquiv : IsPseudolatticeEquiv (P .snd) e (S .snd)
    pres≤ makeIsPseudolatticeEquiv x y = propBiimpl→Equiv
                                          (P.is-pseudolattice .is-prop-valued _ _)
                                          (S.is-pseudolattice .is-prop-valued _ _)
                                          (isMon _ _) (isMonInv' _ _)
      where
      isMonInv' : ∀ x y → equivFun e x S.≤ equivFun e y → x P.≤ y
      isMonInv' x y ex≤ey = transport (λ i → retEq e x i P.≤ retEq e y i) (isMonInv _ _ ex≤ey)


module PseudolatticeReasoning (P' : Pseudolattice ℓ ℓ') where
 private P = fst P'
 open PseudolatticeStr (snd P')
 open IsPseudolattice

 _≤⟨_⟩_ : (x : P) {y z : P} → x ≤ y → y ≤ z → x ≤ z
 x ≤⟨ p ⟩ q = is-pseudolattice .is-trans x _ _ p q

 _◾ : (x : P) → x ≤ x
 x ◾ = is-pseudolattice .is-refl x

 infixr 0 _≤⟨_⟩_
 infix  1 _◾

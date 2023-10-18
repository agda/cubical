{-# OPTIONS --safe #-}
module Cubical.Data.Rationals.Order where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Int.Base as ℤ using ()
open import Cubical.Data.Int.Properties as ℤ using ()
open import Cubical.Data.Int.Order as ℤ using ()
open import Cubical.Data.Rationals.Base
open import Cubical.Data.Rationals.Properties
open import Cubical.Data.Nat as ℕ
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Sigma

open import Cubical.HITs.SetQuotients

open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary.Base

infix 4 _≤_ _<_ _≥_ _>_

private
  _≤'_ : ℚ → ℚ → hProp _
  _≤'_ = rec2 isSetHProp
    (λ { (a , b) (c , d) → (a ℤ.· ℕ₊₁→ℤ d ℤ.≤ c ℤ.· ℕ₊₁→ℤ b) , ℤ.isProp≤ })
    (λ { (a , b) (c , d) (e , f) ad≡cb →
       Σ≡Prop (λ _ → isPropIsProp) (ua (propBiimpl→Equiv ℤ.isProp≤ ℤ.isProp≤
         (ℤ.≤-·o-cancel {k = -1+ b} ∘
          subst2 ℤ._≤_ (sym (ℤ.·Assoc a (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ d)) ∙
                           cong (a ℤ.·_) (ℤ.·Comm (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ d)) ∙
                           ℤ.·Assoc a (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ f) ∙
                           cong (ℤ._· ℕ₊₁→ℤ f) ad≡cb ∙
                           sym (ℤ.·Assoc c (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ f)) ∙
                           cong (c ℤ.·_) (ℤ.·Comm (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ f)) ∙
                           ℤ.·Assoc c (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ b))
                       (sym (ℤ.·Assoc e (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ d)) ∙
                           cong (e ℤ.·_) (ℤ.·Comm (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ d)) ∙
                           ℤ.·Assoc e (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b)) ∘
          ℤ.≤-·o {k = ℕ₊₁→ℕ d})
         (ℤ.≤-·o-cancel {k = -1+ d} ∘
          subst2 ℤ._≤_ (sym (ℤ.·Assoc c (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ b)) ∙
                           cong (c ℤ.·_) (ℤ.·Comm (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ b)) ∙
                           ℤ.·Assoc c (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ f) ∙
                           cong (ℤ._· ℕ₊₁→ℤ f) (sym ad≡cb) ∙
                           sym (ℤ.·Assoc a (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ f)) ∙
                           cong (a ℤ.·_) (ℤ.·Comm (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ f)) ∙
                           ℤ.·Assoc a (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ d))
                        (sym (ℤ.·Assoc e (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b)) ∙
                           cong (e ℤ.·_) (ℤ.·Comm (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b)) ∙
                           ℤ.·Assoc e (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ d)) ∘
          ℤ.≤-·o {k = ℕ₊₁→ℕ b}))) })
     λ { (a , b) (c , d) (e , f) cf≡ed →
       Σ≡Prop (λ _ → isPropIsProp) (ua (propBiimpl→Equiv ℤ.isProp≤ ℤ.isProp≤
         (ℤ.≤-·o-cancel {k = -1+ d} ∘
          subst2 ℤ._≤_ (sym (ℤ.·Assoc a (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ f)) ∙
                           cong (a ℤ.·_) (ℤ.·Comm (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ f)) ∙
                           ℤ.·Assoc a (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ d))
                        (sym (ℤ.·Assoc c (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ f)) ∙
                           cong (c ℤ.·_) (ℤ.·Comm (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ f)) ∙
                           ℤ.·Assoc c (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ b) ∙
                           cong (ℤ._· ℕ₊₁→ℤ b) cf≡ed ∙
                           sym (ℤ.·Assoc e (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b)) ∙
                           cong (e ℤ.·_) (ℤ.·Comm (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b)) ∙
                           ℤ.·Assoc e (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ d)) ∘
          ℤ.≤-·o {k = ℕ₊₁→ℕ f})
         (ℤ.≤-·o-cancel {k = -1+ f} ∘
          subst2 ℤ._≤_ (sym (ℤ.·Assoc a (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ d)) ∙
                           cong (a ℤ.·_) (ℤ.·Comm (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ d)) ∙
                           ℤ.·Assoc a (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ f))
                          (sym (ℤ.·Assoc e (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ d)) ∙
                           cong (e ℤ.·_) (ℤ.·Comm (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ d)) ∙
                           ℤ.·Assoc e (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b) ∙
                           cong (ℤ._· ℕ₊₁→ℤ b) (sym cf≡ed) ∙
                           sym (ℤ.·Assoc c (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ b)) ∙
                           cong (c ℤ.·_) (ℤ.·Comm (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ b)) ∙
                           ℤ.·Assoc c (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ f)) ∘
          ℤ.≤-·o {k = ℕ₊₁→ℕ d}))) }

  _<'_ : ℚ → ℚ → hProp _
  _<'_ = rec2 isSetHProp
    (λ { (a , b) (c , d) → (a ℤ.· ℕ₊₁→ℤ d ℤ.< c ℤ.· ℕ₊₁→ℤ b) , ℤ.isProp< })
    (λ { (a , b) (c , d) (e , f) ad≡cb →
       Σ≡Prop (λ _ → isPropIsProp) (ua (propBiimpl→Equiv ℤ.isProp< ℤ.isProp<
         (ℤ.<-·o-cancel {k = -1+ b} ∘
          subst2 ℤ._<_ (sym (ℤ.·Assoc a (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ d)) ∙
                           cong (a ℤ.·_) (ℤ.·Comm (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ d)) ∙
                           ℤ.·Assoc a (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ f) ∙
                           cong (ℤ._· ℕ₊₁→ℤ f) ad≡cb ∙
                           sym (ℤ.·Assoc c (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ f)) ∙
                           cong (c ℤ.·_) (ℤ.·Comm (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ f)) ∙
                           ℤ.·Assoc c (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ b))
                       (sym (ℤ.·Assoc e (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ d)) ∙
                           cong (e ℤ.·_) (ℤ.·Comm (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ d)) ∙
                           ℤ.·Assoc e (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b)) ∘
          ℤ.<-·o {k = -1+ d})
         (ℤ.<-·o-cancel {k = -1+ d} ∘
          subst2 ℤ._<_ (sym (ℤ.·Assoc c (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ b)) ∙
                           cong (c ℤ.·_) (ℤ.·Comm (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ b)) ∙
                           ℤ.·Assoc c (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ f) ∙
                           cong (ℤ._· ℕ₊₁→ℤ f) (sym ad≡cb) ∙
                           sym (ℤ.·Assoc a (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ f)) ∙
                           cong (a ℤ.·_) (ℤ.·Comm (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ f)) ∙
                           ℤ.·Assoc a (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ d))
                       (sym (ℤ.·Assoc e (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b)) ∙
                           cong (e ℤ.·_) (ℤ.·Comm (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b)) ∙
                           ℤ.·Assoc e (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ d)) ∘
          ℤ.<-·o {k = -1+ b}))) })
     λ { (a , b) (c , d) (e , f) cf≡ed →
       Σ≡Prop (λ _ → isPropIsProp) (ua (propBiimpl→Equiv ℤ.isProp< ℤ.isProp<
         (ℤ.<-·o-cancel {k = -1+ d} ∘
          subst2 ℤ._<_ (sym (ℤ.·Assoc a (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ f)) ∙
                           cong (a ℤ.·_) (ℤ.·Comm (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ f)) ∙
                           ℤ.·Assoc a (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ d))
                        (sym (ℤ.·Assoc c (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ f)) ∙
                           cong (c ℤ.·_) (ℤ.·Comm (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ f)) ∙
                           ℤ.·Assoc c (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ b) ∙
                           cong (ℤ._· ℕ₊₁→ℤ b) cf≡ed ∙
                           sym (ℤ.·Assoc e (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b)) ∙
                           cong (e ℤ.·_) (ℤ.·Comm (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b)) ∙
                           ℤ.·Assoc e (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ d)) ∘
          ℤ.<-·o {k = -1+ f})
         (ℤ.<-·o-cancel {k = -1+ f} ∘
          subst2 ℤ._<_ (sym (ℤ.·Assoc a (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ d)) ∙
                           cong (a ℤ.·_) (ℤ.·Comm (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ d)) ∙
                           ℤ.·Assoc a (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ f))
                       (sym (ℤ.·Assoc e (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ d)) ∙
                           cong (e ℤ.·_) (ℤ.·Comm (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ d)) ∙
                           ℤ.·Assoc e (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b) ∙
                           cong (ℤ._· ℕ₊₁→ℤ b) (sym cf≡ed) ∙
                           sym (ℤ.·Assoc c (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ b)) ∙
                           cong (c ℤ.·_) (ℤ.·Comm (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ b)) ∙
                           ℤ.·Assoc c (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ f)) ∘
          ℤ.<-·o {k = -1+ d}))) }

_≤_ : ℚ → ℚ → Type
m ≤ n = fst (m ≤' n)

_<_ : ℚ → ℚ → Type
m < n = fst (m <' n)

_≥_ : ℚ → ℚ → Type
m ≥ n = n ≤ m

_>_ : ℚ → ℚ → Type
m > n = n < m

module _ where
  open BinaryRelation

  isProp≤ : isPropValued _≤_
  isProp≤ m n = snd (m ≤' n)

  isProp< : isPropValued _<_
  isProp< m n = snd (m <' n)

  isRefl≤ : isRefl _≤_
  isRefl≤ = elimProp {P = λ x → x ≤ x} (λ x → isProp≤ x x) λ _ → ℤ.isRefl≤

  isIrrefl< : isIrrefl _<_
  isIrrefl< = elimProp {P = λ x → ¬ x < x} (λ _ → isProp¬ _) λ _ → ℤ.isIrrefl<

  isAntisym≤ : isAntisym _≤_
  isAntisym≤ =
    elimProp2 {P = λ a b → a ≤ b → b ≤ a → a ≡ b}
              (λ x y → isPropΠ2 λ _ _ → isSetℚ x y)
              λ a b a≤b b≤a → eq/ a b (ℤ.isAntisym≤ a≤b b≤a)

  isTrans≤ : isTrans _≤_
  isTrans≤ =
    elimProp3 {P = λ a b c → a ≤ b → b ≤ c → a ≤ c}
              (λ x y z → isPropΠ2 λ _ _ → isProp≤ x z)
              λ { (a , b) (c , d) (e , f) ad≤cb cf≤ed →
                ℤ.≤-·o-cancel {k = -1+ d}
                  (subst (ℤ._≤ e ℤ.· ℕ₊₁→ℤ b ℤ.· ℕ₊₁→ℤ d)
                    ((sym (ℤ.·Assoc a (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ f)) ∙
                      cong (a ℤ.·_) (ℤ.·Comm (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ f))) ∙
                      ℤ.·Assoc a (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ d))
                  (ℤ.isTrans≤ (ℤ.≤-·o {k = ℕ₊₁→ℕ f} ad≤cb)
                    (subst2 ℤ._≤_
                      (sym (ℤ.·Assoc c (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ b)) ∙
                        cong (c ℤ.·_) (ℤ.·Comm (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ b)) ∙
                        ℤ.·Assoc c (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ f))
                      (sym (ℤ.·Assoc e (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b)) ∙
                        cong (e ℤ.·_) (ℤ.·Comm (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b)) ∙
                        ℤ.·Assoc e (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ d))
                      (ℤ.≤-·o {k = ℕ₊₁→ℕ b} cf≤ed)))) }

  isTrans< : isTrans _<_
  isTrans< =
    elimProp3 {P = λ a b c → a < b → b < c → a < c}
              (λ x y z → isPropΠ2 λ _ _ → isProp< x z)
              λ { (a , b) (c , d) (e , f) ad<cb cf<ed →
                ℤ.<-·o-cancel {k = -1+ d}
                  (subst (ℤ._< e ℤ.· ℕ₊₁→ℤ b ℤ.· ℕ₊₁→ℤ d)
                    ((sym (ℤ.·Assoc a (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ f)) ∙
                      cong (a ℤ.·_) (ℤ.·Comm (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ f))) ∙
                      ℤ.·Assoc a (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ d))
                  (ℤ.isTrans< (ℤ.<-·o {k = -1+ f} ad<cb)
                    (subst2 ℤ._<_
                      (sym (ℤ.·Assoc c (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ b)) ∙
                        cong (c ℤ.·_) (ℤ.·Comm (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ b)) ∙
                        ℤ.·Assoc c (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ f))
                      (sym (ℤ.·Assoc e (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b)) ∙
                        cong (e ℤ.·_) (ℤ.·Comm (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b)) ∙
                        ℤ.·Assoc e (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ d))
                      (ℤ.<-·o {k = -1+ b} cf<ed)))) }

  isAsym< : isAsym _<_
  isAsym< = isIrrefl×isTrans→isAsym _<_ (isIrrefl< , isTrans<)

{-# OPTIONS --safe #-}
module Cubical.Data.Rationals.Order where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence

open import Cubical.Functions.Logic using (_⊔′_; ⇔toPath)

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Int.Base as ℤ using (ℤ)
open import Cubical.Data.Int.Properties as ℤ using ()
open import Cubical.Data.Int.Order as ℤ using ()
open import Cubical.Data.Int.Divisibility as ℤ
open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Data.Rationals.Properties as ℚ
open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Nat.Mod as ℕ
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎ using (_⊎_; inl; inr; isProp⊎)

open import Cubical.HITs.PropositionalTruncation as ∥₁ using (isPropPropTrunc; ∣_∣₁)
open import Cubical.HITs.SetQuotients

open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary.Base

infix 4 _≤_ _<_ _≥_ _>_

private
  ·CommR : (a b c : ℤ) → a ℤ.· b ℤ.· c ≡ a ℤ.· c ℤ.· b
  ·CommR a b c = sym (ℤ.·Assoc a b c) ∙ cong (a ℤ.·_) (ℤ.·Comm b c) ∙ ℤ.·Assoc a c b

  _≤'_ : ℚ → ℚ → hProp ℓ-zero
  _≤'_ = fun
    where
        lemma≤ : ((a , b) (c , d) (e , f) : (ℤ × ℕ₊₁))
                → (c ℤ.· ℕ₊₁→ℤ f ) ≡ (e ℤ.· ℕ₊₁→ℤ d)
                → ((a ℤ.· ℕ₊₁→ℤ d) ℤ.≤ (c ℤ.· ℕ₊₁→ℤ b))
                ≡ ((a ℤ.· ℕ₊₁→ℤ f) ℤ.≤ (e ℤ.· ℕ₊₁→ℤ b))
        lemma≤ (a , b) (c , d) (e , f) cf≡ed = (ua (propBiimpl→Equiv ℤ.isProp≤ ℤ.isProp≤
                (ℤ.≤-·o-cancel {k = -1+ d} ∘
                  subst2 ℤ._≤_ (·CommR a (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ f))
                               (·CommR c (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ f) ∙
                                cong (ℤ._· ℕ₊₁→ℤ b) cf≡ed ∙
                                ·CommR e (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b)) ∘
                 ℤ.≤-·o {k = ℕ₊₁→ℕ f})
                (ℤ.≤-·o-cancel {k = -1+ f} ∘
                  subst2 ℤ._≤_ (·CommR a (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ d))
                                (·CommR e (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ d) ∙
                                 cong (ℤ._· ℕ₊₁→ℤ b) (sym cf≡ed) ∙
                                 ·CommR c (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ b)) ∘
                 ℤ.≤-·o {k = ℕ₊₁→ℕ d})))

        fun₀ : ℤ × ℕ₊₁ → ℚ → hProp ℓ-zero
        fst (fun₀ (a , b) [ c , d ]) = a ℤ.· ℕ₊₁→ℤ d ℤ.≤ c ℤ.· ℕ₊₁→ℤ b
        snd (fun₀ _ [ _ ]) = ℤ.isProp≤
        fun₀ a/b (eq/ c/d e/f cf≡ed i) = record
          { fst = lemma≤ a/b c/d e/f cf≡ed i
          ; snd = isProp→PathP (λ i → isPropIsProp {A = lemma≤ a/b c/d e/f cf≡ed i}) ℤ.isProp≤ ℤ.isProp≤ i
          }
        fun₀ a/b (squash/ x y p q i j) = isSet→SquareP (λ _ _ → isSetHProp)
          (λ _ → fun₀ a/b x)
          (λ _ → fun₀ a/b y)
          (λ i → fun₀ a/b (p i))
          (λ i → fun₀ a/b (q i)) j i

        toPath : ∀ a/b c/d (x : a/b ∼ c/d) (y : ℚ) → fun₀ a/b y ≡ fun₀ c/d y
        toPath (a , b) (c , d) ad≡cb = elimProp (λ _ → isSetHProp _ _) λ (e , f) →
          Σ≡Prop (λ _ → isPropIsProp) (ua (propBiimpl→Equiv ℤ.isProp≤ ℤ.isProp≤
                (ℤ.≤-·o-cancel {k = -1+ b} ∘
                  subst2 ℤ._≤_ (·CommR a (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ d) ∙
                                 cong (ℤ._· ℕ₊₁→ℤ f) ad≡cb ∙
                                 ·CommR c (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ f))
                               (·CommR e (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ d)) ∘
                 ℤ.≤-·o {k = ℕ₊₁→ℕ d})
                (ℤ.≤-·o-cancel {k = -1+ d} ∘
                  subst2 ℤ._≤_ (·CommR c (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ b) ∙
                                 cong (ℤ._· ℕ₊₁→ℤ f) (sym ad≡cb) ∙
                                 ·CommR a (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ f))
                               (·CommR e (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b)) ∘
                 ℤ.≤-·o {k = ℕ₊₁→ℕ b})))

        fun : ℚ → ℚ → hProp ℓ-zero
        fun [ a/b ] y = fun₀ a/b y
        fun (eq/ a/b c/d ad≡cb i) y = toPath a/b c/d ad≡cb y i
        fun (squash/ x y p q i j) z = isSet→SquareP (λ _ _ → isSetHProp)
          (λ _ → fun x z) (λ _ → fun y z) (λ i → fun (p i) z) (λ i → fun (q i) z) j i

  _<'_ : ℚ → ℚ → hProp ℓ-zero
  _<'_ = fun
    where
        lemma< : ((a , b) (c , d) (e , f) : (ℤ × ℕ₊₁))
                → (c ℤ.· ℕ₊₁→ℤ f ) ≡ (e ℤ.· ℕ₊₁→ℤ d)
                → ((a ℤ.· ℕ₊₁→ℤ d) ℤ.< (c ℤ.· ℕ₊₁→ℤ b))
                ≡ ((a ℤ.· ℕ₊₁→ℤ f) ℤ.< (e ℤ.· ℕ₊₁→ℤ b))
        lemma< (a , b) (c , d) (e , f) cf≡ed = (ua (propBiimpl→Equiv ℤ.isProp< ℤ.isProp<
                (ℤ.<-·o-cancel {k = -1+ d} ∘
                  subst2 ℤ._<_ (·CommR a (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ f))
                               (·CommR c (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ f) ∙
                                cong (ℤ._· ℕ₊₁→ℤ b) cf≡ed ∙
                                ·CommR e (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b)) ∘
                 ℤ.<-·o {k = -1+ f})
                (ℤ.<-·o-cancel {k = -1+ f} ∘
                  subst2 ℤ._<_ (·CommR a (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ d))
                               (·CommR e (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ d) ∙
                                cong (ℤ._· ℕ₊₁→ℤ b) (sym cf≡ed) ∙
                                ·CommR c (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ b)) ∘
                 ℤ.<-·o {k = -1+ d})))

        fun₀ : ℤ × ℕ₊₁ → ℚ → hProp ℓ-zero
        fst (fun₀ (a , b) [ c , d ]) = a ℤ.· ℕ₊₁→ℤ d ℤ.< c ℤ.· ℕ₊₁→ℤ b
        snd (fun₀ _ [ _ ]) = ℤ.isProp<
        fun₀ a/b (eq/ c/d e/f cf≡ed i) = record
          { fst = lemma< a/b c/d e/f cf≡ed i
          ; snd = isProp→PathP (λ i → isPropIsProp {A = lemma< a/b c/d e/f cf≡ed i}) ℤ.isProp< ℤ.isProp< i
          }
        fun₀ a/b (squash/ x y p q i j) = isSet→SquareP (λ _ _ → isSetHProp)
          (λ _ → fun₀ a/b x)
          (λ _ → fun₀ a/b y)
          (λ i → fun₀ a/b (p i))
          (λ i → fun₀ a/b (q i)) j i

        toPath : ∀ a/b c/d (x : a/b ∼ c/d) (y : ℚ) → fun₀ a/b y ≡ fun₀ c/d y
        toPath (a , b) (c , d) ad≡cb = elimProp (λ _ → isSetHProp _ _) λ (e , f) →
          Σ≡Prop (λ _ → isPropIsProp) (ua (propBiimpl→Equiv ℤ.isProp< ℤ.isProp<
                (ℤ.<-·o-cancel {k = -1+ b} ∘
                  subst2 ℤ._<_ (·CommR a (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ d) ∙
                                cong (ℤ._· ℕ₊₁→ℤ f) ad≡cb ∙
                                ·CommR c (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ f))
                               (·CommR e (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ d)) ∘
                 ℤ.<-·o {k = -1+ d})
                (ℤ.<-·o-cancel {k = -1+ d} ∘
                  subst2 ℤ._<_ (·CommR c (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ b) ∙
                                cong (ℤ._· ℕ₊₁→ℤ f) (sym ad≡cb) ∙
                                ·CommR a (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ f))
                               (·CommR e (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b)) ∘
                 ℤ.<-·o {k = -1+ b})))

        fun : ℚ → ℚ → hProp ℓ-zero
        fun [ a/b ] y = fun₀ a/b y
        fun (eq/ a/b c/d ad≡cb i) y = toPath a/b c/d ad≡cb y i
        fun (squash/ x y p q i j) z = isSet→SquareP (λ _ _ → isSetHProp)
          (λ _ → fun x z) (λ _ → fun y z) (λ i → fun (p i) z) (λ i → fun (q i) z) j i

_≤_ : ℚ → ℚ → Type₀
m ≤ n = fst (m ≤' n)

_<_ : ℚ → ℚ → Type₀
m < n = fst (m <' n)

_≥_ : ℚ → ℚ → Type₀
m ≥ n = n ≤ m

_>_ : ℚ → ℚ → Type₀
m > n = n < m

_#_ : ℚ → ℚ → Type₀
m # n = (m < n) ⊎ (n < m)

data Trichotomy (m n : ℚ) : Type₀ where
  lt : m < n → Trichotomy m n
  eq : m ≡ n → Trichotomy m n
  gt : m > n → Trichotomy m n

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
              (λ x _ z → isPropΠ2 λ _ _ → isProp≤ x z)
              λ { (a , b) (c , d) (e , f) ad≤cb cf≤ed →
                ℤ.≤-·o-cancel {k = -1+ d}
                  (subst (ℤ._≤ e ℤ.· ℕ₊₁→ℤ b ℤ.· ℕ₊₁→ℤ d)
                    (·CommR a (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ f))
                  (ℤ.isTrans≤ (ℤ.≤-·o {k = ℕ₊₁→ℕ f} ad≤cb)
                    (subst2 ℤ._≤_
                      (·CommR c (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ b))
                      (·CommR e (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b))
                      (ℤ.≤-·o {k = ℕ₊₁→ℕ b} cf≤ed)))) }

  isTrans< : isTrans _<_
  isTrans< =
    elimProp3 {P = λ a b c → a < b → b < c → a < c}
              (λ x _ z → isPropΠ2 λ _ _ → isProp< x z)
              λ { (a , b) (c , d) (e , f) ad<cb cf<ed →
                ℤ.<-·o-cancel {k = -1+ d}
                  (subst (ℤ._< e ℤ.· ℕ₊₁→ℤ b ℤ.· ℕ₊₁→ℤ d)
                    (·CommR a (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ f))
                  (ℤ.isTrans< (ℤ.<-·o {k = -1+ f} ad<cb)
                    (subst2 ℤ._<_
                      (·CommR c (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ b))
                      (·CommR e (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b))
                      (ℤ.<-·o {k = -1+ b} cf<ed)))) }

  isAsym< : isAsym _<_
  isAsym< = isIrrefl×isTrans→isAsym _<_ (isIrrefl< , isTrans<)

  isStronglyConnected≤ : isStronglyConnected _≤_
  isStronglyConnected≤ =
    elimProp2 {P = λ a b → (a ≤ b) ⊔′ (b ≤ a)}
              (λ _ _ → isPropPropTrunc)
               λ a b → ∣ lem a b ∣₁
    where
      lem : (a b : ℤ.ℤ × ℕ₊₁) → ([ a ] ≤ [ b ]) ⊎ ([ b ] ≤ [ a ])
      lem (a , b) (c , d) with (a ℤ.· ℕ₊₁→ℤ d) ℤ.≟ (c ℤ.· ℕ₊₁→ℤ b)
      ... | ℤ.lt ad<cb = inl (ℤ.<-weaken ad<cb)
      ... | ℤ.eq ad≡cb = inl (0 , ad≡cb)
      ... | ℤ.gt cb<ad = inr (ℤ.<-weaken cb<ad)

  isConnected< : isConnected _<_
  isConnected< =
    elimProp2 {P = λ a b → ¬ a ≡ b → (a < b) ⊔′ (b < a)}
              (λ _ _ → isProp→ isPropPropTrunc)
               λ a b ¬a≡b → ∣ lem a b ¬a≡b ∣₁
    where
      -- Agda can't infer the relation involved, so the signature looks a bit weird here
      lem : (a b : ℤ.ℤ × ℕ₊₁) → ¬ [_] {R = _∼_} a ≡ [ b ] → ([ a ] < [ b ]) ⊎ ([ b ] < [ a ])
      lem (a , b) (c , d) ¬a≡b with (a ℤ.· ℕ₊₁→ℤ d) ℤ.≟ (c ℤ.· ℕ₊₁→ℤ b)
      ... | ℤ.lt ad<cb = inl ad<cb
      ... | ℤ.eq ad≡cb = ⊥.rec (¬a≡b (eq/ (a , b) (c , d) ad≡cb))
      ... | ℤ.gt cb<ad = inr cb<ad

  isWeaklyLinear< : isWeaklyLinear _<_
  isWeaklyLinear< =
    elimProp3 {P = λ a b c → a < b → (a < c) ⊔′ (c < b)}
              (λ _ _ _ → isProp→ isPropPropTrunc)
               lem
    where
      lem : (a b c : ℤ.ℤ × ℕ₊₁) → [ a ] < [ b ] → ([ a ] < [ c ]) ⊔′ ([ c ] < [ b ])
      lem a b c a<b with discreteℚ [ a ] [ c ]
      ... | yes a≡c = ∣ inr (subst (_< [ b ]) a≡c a<b) ∣₁
      ... | no a≢c = ∥₁.map (⊎.map (λ a<c → a<c)
                                    (λ c<a → isTrans< [ c ] [ a ] [ b ] c<a a<b))
                             (isConnected< [ a ] [ c ] a≢c)

  isProp# : isPropValued _#_
  isProp# x y = isProp⊎ (isProp< x y) (isProp< y x) (isAsym< x y)

  isIrrefl# : isIrrefl _#_
  isIrrefl# x (inl x<x) = isIrrefl< x x<x
  isIrrefl# x (inr x<x) = isIrrefl< x x<x

  isSym# : isSym _#_
  isSym# _ _ (inl x<y) = inr x<y
  isSym# _ _ (inr y<x) = inl y<x

  isCotrans# : isCotrans _#_
  isCotrans#
    = elimProp3 {P = λ a b c → a # b → (a # c) ⊔′ (b # c)}
                (λ _ _ _ → isProp→ isPropPropTrunc)
                 lem
      where
        lem : (a b c : ℤ.ℤ × ℕ₊₁) → [ a ] # [ b ] → ([ a ] # [ c ]) ⊔′ ([ b ] # [ c ])
        lem a b c a#b with discreteℚ [ b ] [ c ]
        ... | yes b≡c = ∣ inl (subst ([ a ] #_) b≡c a#b) ∣₁
        ... | no  b≢c = ∥₁.map inr (isConnected< [ b ] [ c ] b≢c)

  inequalityImplies# : inequalityImplies _#_
  inequalityImplies# a b = ∥₁.rec (isProp# a b) (λ a#b → a#b) ∘ (isConnected< a b)

≤-+o : ∀ m n o → m ≤ n → m ℚ.+ o ≤ n ℚ.+ o
≤-+o =
  elimProp3 {P = λ a b c → a ≤ b → a ℚ.+ c ≤ b ℚ.+ c}
            (λ x y z → isProp→ (isProp≤ (x ℚ.+ z) (y ℚ.+ z)))
             λ { (a , b) (c , d) (e , f) ad≤cb →
               subst2 ℤ._≤_
                       (cong₂ ℤ._+_
                              (cong (λ x → a ℤ.· ℕ₊₁→ℤ d ℤ.· x)
                                    (ℤ.pos·pos (ℕ₊₁→ℕ f) (ℕ₊₁→ℕ f)) ∙
                                    sym (ℤ.·Assoc a (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ f ℤ.· ℕ₊₁→ℤ f)) ∙
                                    cong (a ℤ.·_) (ℤ.·Assoc (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ f) ∙
                                    cong (ℤ._· ℕ₊₁→ℤ f) (ℤ.·Comm (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ f)) ∙
                                    sym (ℤ.·Assoc (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ f))) ∙
                                    ℤ.·Assoc a (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ d ℤ.· ℕ₊₁→ℤ f) ∙
                                    cong (λ x → a ℤ.· ℕ₊₁→ℤ f ℤ.· x)
                                         (sym (ℤ.pos·pos (ℕ₊₁→ℕ d) (ℕ₊₁→ℕ f))))
                              (sym (ℤ.·Assoc (e ℤ.· ℕ₊₁→ℤ b) (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ f)) ∙
                                   cong (λ x → e ℤ.· ℕ₊₁→ℤ b ℤ.· x)
                                        (sym (ℤ.pos·pos (ℕ₊₁→ℕ d) (ℕ₊₁→ℕ f)))) ∙
                              sym (ℤ.·DistL+ (a ℤ.· ℕ₊₁→ℤ f) (e ℤ.· ℕ₊₁→ℤ b) (ℕ₊₁→ℤ (d ·₊₁ f))))
                       (cong₂ ℤ._+_
                              (cong (λ x → c ℤ.· ℕ₊₁→ℤ b ℤ.· x)
                                    (ℤ.pos·pos (ℕ₊₁→ℕ f) (ℕ₊₁→ℕ f)) ∙
                                    sym (ℤ.·Assoc c (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ f ℤ.· ℕ₊₁→ℤ f)) ∙
                                    cong (c ℤ.·_) (ℤ.·Assoc (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ f) ∙
                                    cong (ℤ._· ℕ₊₁→ℤ f) (ℤ.·Comm (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ f)) ∙
                                    sym (ℤ.·Assoc (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ f))) ∙
                                    ℤ.·Assoc c (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ b ℤ.· ℕ₊₁→ℤ f) ∙
                                    cong (λ x → c ℤ.· ℕ₊₁→ℤ f ℤ.· x)
                                         (sym (ℤ.pos·pos (ℕ₊₁→ℕ b) (ℕ₊₁→ℕ f))))
                              (cong (ℤ._· ℕ₊₁→ℤ f)
                                    (sym (ℤ.·Assoc e (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ d)) ∙
                                    cong (e ℤ.·_) (ℤ.·Comm (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ d)) ∙
                                    ℤ.·Assoc e (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b)) ∙
                                    sym (ℤ.·Assoc (e ℤ.· ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ f)) ∙
                                    cong (λ x → e ℤ.· ℕ₊₁→ℤ d ℤ.· x)
                                         (sym (ℤ.pos·pos (ℕ₊₁→ℕ b) (ℕ₊₁→ℕ f)))) ∙
                       sym (ℤ.·DistL+ (c ℤ.· ℕ₊₁→ℤ f) (e ℤ.· ℕ₊₁→ℤ d) (ℕ₊₁→ℤ (b ·₊₁ f))))
                       (ℤ.≤-+o {o = e ℤ.· ℕ₊₁→ℤ b ℤ.· ℕ₊₁→ℤ d ℤ.· ℕ₊₁→ℤ f}
                               (ℤ.≤-·o {k = ℕ₊₁→ℕ (f ·₊₁ f)} ad≤cb)) }

≤-o+ : ∀ m n o →  m ≤ n → o ℚ.+ m ≤ o ℚ.+ n
≤-o+ m n o = subst2 _≤_ (+Comm m o)
                         (+Comm n o) ∘
             ≤-+o m n o

≤Monotone+ : ∀ m n o s → m ≤ n → o ≤ s → m ℚ.+ o ≤ n ℚ.+ s
≤Monotone+ m n o s m≤n o≤s
  = isTrans≤ (m ℚ.+ o)
              (n ℚ.+ o)
              (n ℚ.+ s)
              (≤-+o m n o m≤n)
              (≤-o+ o s n o≤s)

≤-o+-cancel : ∀ m n o →  o ℚ.+ m ≤ o ℚ.+ n → m ≤ n
≤-o+-cancel m n o
  = subst2 _≤_ (+Assoc (- o) o m ∙ cong (ℚ._+ m) (+InvL o) ∙ +IdL m)
                (+Assoc (- o) o n ∙ cong (ℚ._+ n) (+InvL o) ∙ +IdL n) ∘
           ≤-o+ (o ℚ.+ m) (o ℚ.+ n) (- o)

≤-+o-cancel : ∀ m n o → m ℚ.+ o ≤ n ℚ.+ o → m ≤ n
≤-+o-cancel m n o
  = subst2 _≤_ (sym (+Assoc m o (- o)) ∙ cong (λ x → m ℚ.+ x) (+InvR o) ∙ +IdR m)
                (sym (+Assoc n o (- o)) ∙ cong (λ x → n ℚ.+ x) (+InvR o) ∙ +IdR n) ∘
           ≤-+o (m ℚ.+ o) (n ℚ.+ o) (- o)

<-+o : ∀ m n o → m < n → m ℚ.+ o < n ℚ.+ o
<-+o =
  elimProp3 {P = λ a b c → a < b → a ℚ.+ c < b ℚ.+ c}
            (λ x y z → isProp→ (isProp< (x ℚ.+ z) (y ℚ.+ z)))
             λ { (a , b) (c , d) (e , f) ad<cb →
               subst2 ℤ._<_
                       (cong₂ ℤ._+_
                              (cong (λ x → a ℤ.· ℕ₊₁→ℤ d ℤ.· x)
                                    (ℤ.pos·pos (ℕ₊₁→ℕ f) (ℕ₊₁→ℕ f)) ∙
                                    sym (ℤ.·Assoc a (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ f ℤ.· ℕ₊₁→ℤ f)) ∙
                                    cong (a ℤ.·_) (ℤ.·Assoc (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ f) ∙
                                    cong (ℤ._· ℕ₊₁→ℤ f) (ℤ.·Comm (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ f)) ∙
                                    sym (ℤ.·Assoc (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ f))) ∙
                                    ℤ.·Assoc a (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ d ℤ.· ℕ₊₁→ℤ f) ∙
                                    cong (λ x → a ℤ.· ℕ₊₁→ℤ f ℤ.· x)
                                         (sym (ℤ.pos·pos (ℕ₊₁→ℕ d) (ℕ₊₁→ℕ f))))
                              (sym (ℤ.·Assoc (e ℤ.· ℕ₊₁→ℤ b) (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ f)) ∙
                                   cong (λ x → e ℤ.· ℕ₊₁→ℤ b ℤ.· x)
                                        (sym (ℤ.pos·pos (ℕ₊₁→ℕ d) (ℕ₊₁→ℕ f)))) ∙
                       sym (ℤ.·DistL+ (a ℤ.· ℕ₊₁→ℤ f) (e ℤ.· ℕ₊₁→ℤ b) (ℕ₊₁→ℤ (d ·₊₁ f))))
                       (cong₂ ℤ._+_
                              (cong (λ x → c ℤ.· ℕ₊₁→ℤ b ℤ.· x)
                                    (ℤ.pos·pos (ℕ₊₁→ℕ f) (ℕ₊₁→ℕ f)) ∙
                                    sym (ℤ.·Assoc c (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ f ℤ.· ℕ₊₁→ℤ f)) ∙
                                    cong (c ℤ.·_) (ℤ.·Assoc (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ f) ∙
                                    cong (ℤ._· ℕ₊₁→ℤ f) (ℤ.·Comm (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ f)) ∙
                                    sym (ℤ.·Assoc (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ f))) ∙
                                    ℤ.·Assoc c (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ b ℤ.· ℕ₊₁→ℤ f) ∙
                                    cong (λ x → c ℤ.· ℕ₊₁→ℤ f ℤ.· x)
                                         (sym (ℤ.pos·pos (ℕ₊₁→ℕ b) (ℕ₊₁→ℕ f))))
                              (cong (ℤ._· ℕ₊₁→ℤ f)
                                    (sym (ℤ.·Assoc e (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ d)) ∙
                                    cong (e ℤ.·_) (ℤ.·Comm (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ d)) ∙
                                    ℤ.·Assoc e (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b)) ∙
                                    sym (ℤ.·Assoc (e ℤ.· ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ f)) ∙
                                    cong (λ x → e ℤ.· ℕ₊₁→ℤ d ℤ.· x)
                                         (sym (ℤ.pos·pos (ℕ₊₁→ℕ b) (ℕ₊₁→ℕ f)))) ∙
                       sym (ℤ.·DistL+ (c ℤ.· ℕ₊₁→ℤ f) (e ℤ.· ℕ₊₁→ℤ d) (ℕ₊₁→ℤ (b ·₊₁ f))))
                       (ℤ.<-+o {o = e ℤ.· ℕ₊₁→ℤ b ℤ.· ℕ₊₁→ℤ d ℤ.· ℕ₊₁→ℤ f}
                               (ℤ.<-·o {k = -1+ (f ·₊₁ f)} ad<cb)) }

<-o+ : ∀ m n o → m < n → o ℚ.+ m < o ℚ.+ n
<-o+ m n o = subst2 _<_ (+Comm m o) (+Comm n o) ∘ <-+o m n o

<Monotone+ : ∀ m n o s → m < n → o < s → m ℚ.+ o < n ℚ.+ s
<Monotone+ m n o s m<n o<s
  = isTrans< (m ℚ.+ o) (n ℚ.+ o) (n ℚ.+ s) (<-+o m n o m<n) (<-o+ o s n o<s)


<-o+-cancel : ∀ m n o → o ℚ.+ m < o ℚ.+ n → m < n
<-o+-cancel m n o
  = subst2 _<_ (+Assoc (- o) o m ∙ cong (ℚ._+ m) (+InvL o) ∙ +IdL m)
               (+Assoc (- o) o n ∙ cong (ℚ._+ n) (+InvL o) ∙ +IdL n) ∘
           <-o+ (o ℚ.+ m) (o ℚ.+ n) (- o)

<-+o-cancel : ∀ m n o → m ℚ.+ o < n ℚ.+ o → m < n
<-+o-cancel m n o
  = subst2 _<_ (sym (+Assoc m o (- o)) ∙ cong (λ x → m ℚ.+ x) (+InvR o) ∙ +IdR m)
               (sym (+Assoc n o (- o)) ∙ cong (λ x → n ℚ.+ x) (+InvR o) ∙ +IdR n) ∘
           <-+o (m ℚ.+ o) (n ℚ.+ o) (- o)

<Weaken≤ : ∀ m n → m < n → m ≤ n
<Weaken≤ m n = elimProp2 {P = λ x y → x < y → x ≤ y}
                             (λ x y → isProp→ (isProp≤ x y))
                             (λ { (a , b) (c , d) → ℤ.<-weaken }) m n


isTrans<≤ : ∀ m n o → m < n → n ≤ o → m < o
isTrans<≤ =
    elimProp3 {P = λ a b c → a < b → b ≤ c → a < c}
              (λ x _ z → isPropΠ2 λ _ _ → isProp< x z)
               λ { (a , b) (c , d) (e , f) ad<cb cf≤ed
                → ℤ.<-·o-cancel {k = -1+ d}
                 (ℤ.<≤-trans {m = c ℤ.· ℕ₊₁→ℤ f ℤ.· ℕ₊₁→ℤ b}
                              (subst2 ℤ._<_ (·CommR a (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ f))
                                            (·CommR c (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ f))
                                            (ℤ.<-·o {k = -1+ f} ad<cb))
                              (subst (_ ℤ.≤_) (·CommR e (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b))
                                     (ℤ.≤-·o {k = ℕ₊₁→ℕ b} cf≤ed)) )}

isTrans≤< : ∀ m n o → m ≤ n → n < o → m < o
isTrans≤< =
    elimProp3 {P = λ a b c → a ≤ b → b < c → a < c}
              (λ x _ z → isPropΠ2 λ _ _ → isProp< x z)
               λ { (a , b) (c , d) (e , f) ad≤cb cf<ed
                → ℤ.<-·o-cancel {k = -1+ d}
                 (ℤ.≤<-trans {m = c ℤ.· ℕ₊₁→ℤ f ℤ.· ℕ₊₁→ℤ b}
                              (subst2 ℤ._≤_ (·CommR a (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ f))
                                             (·CommR c (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ f))
                                             (ℤ.≤-·o {k = ℕ₊₁→ℕ f} ad≤cb))
                              (subst (_ ℤ.<_) (·CommR e (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b))
                                     (ℤ.<-·o {k = -1+ b} cf<ed)) )}


<≤Monotone+ : ∀ m n o s → m < n → o ≤ s → m ℚ.+ o < n ℚ.+ s
<≤Monotone+ m n o s x x₁ =
   isTrans<≤ (m ℚ.+ o) (n ℚ.+ o) (n ℚ.+ s) (<-+o m n o x) (≤-o+ o s n x₁)

≤<Monotone+ : ∀ m n o s → m ≤ n → o < s → m ℚ.+ o < n ℚ.+ s
≤<Monotone+ m n o s x x₁ =
   isTrans≤< (m ℚ.+ o) (n ℚ.+ o) (n ℚ.+ s) (≤-+o m n o x) (<-o+ o s n x₁)


<Weaken+nonNeg : ∀ m n o → m < n → 0 ≤ o → m < (n ℚ.+ o)
<Weaken+nonNeg m n o u v =
  subst (_< (n ℚ.+ o)) (ℚ.+IdR m) (<≤Monotone+ m n 0 o u v)

<WeakenNonNeg+ : ∀ m n o → m < n → 0 ≤ o → m < (o ℚ.+ n)
<WeakenNonNeg+ m n o u v =
  subst (_< (o ℚ.+ n)) (ℚ.+IdL m) (≤<Monotone+ 0 o m n v u)


≤-·o : ∀ m n o → 0 ≤ o → m ≤ n → m ℚ.· o ≤ n ℚ.· o
≤-·o =
  elimProp3 {P = λ a b c → 0 ≤ c → a ≤ b → a ℚ.· c ≤ b ℚ.· c}
            (λ x y z → isPropΠ2 λ _ _ → isProp≤ (x ℚ.· z) (y ℚ.· z))
             λ { (a , b) (c , d) (e , f) 0≤e ad≤cb
             → subst2 ℤ._≤_ (cong (ℤ._· ℕ₊₁→ℤ f) (·CommR a (ℕ₊₁→ℤ d) e) ∙
                              sym (ℤ.·Assoc (a ℤ.· e) (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ f)) ∙
                              cong (a ℤ.· e ℤ.·_) (sym (ℤ.pos·pos (ℕ₊₁→ℕ d) (ℕ₊₁→ℕ f))))
                             (cong (ℤ._· ℕ₊₁→ℤ f) (·CommR c (ℕ₊₁→ℤ b) e) ∙
                              sym (ℤ.·Assoc (c ℤ.· e) (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ f)) ∙
                              cong (c ℤ.· e ℤ.·_) (sym (ℤ.pos·pos (ℕ₊₁→ℕ b) (ℕ₊₁→ℕ f))))
                             (ℤ.≤-·o {k = ℕ₊₁→ℕ f}
                                      (ℤ.0≤o→≤-·o (subst (0 ℤ.≤_) (ℤ.·IdR e) 0≤e) ad≤cb)) }

≤-o· : ∀ m n o → 0 ≤ o → m ≤ n → o ℚ.· m ≤ o ℚ.· n
≤-o· m n o x = subst2 _≤_ (·Comm m o)
                         (·Comm n o) ∘
             ≤-·o m n o x


≤-·o-cancel : ∀ m n o → 0 < o → m ℚ.· o ≤ n ℚ.· o → m ≤ n
≤-·o-cancel =
  elimProp3 {P = λ a b c → 0 < c → a ℚ.· c ≤ b ℚ.· c → a ≤ b}
            (λ x y _ → isPropΠ2 λ _ _ → isProp≤ x y)
             λ { (a , b) (c , d) (e , f) 0<e aedf≤cebf
             → ℤ.0<o→≤-·o-cancel (subst (0 ℤ.<_) (ℤ.·IdR e) 0<e)
               (subst2 ℤ._≤_ (·CommR a e (ℕ₊₁→ℤ d)) (·CommR c e (ℕ₊₁→ℤ b))
                      (ℤ.≤-·o-cancel {k = -1+ f}
                        (subst2 ℤ._≤_ (sym (ℤ.·Assoc a e (ℕ₊₁→ℤ (d ·₊₁ f))) ∙
                                       cong (λ x → a ℤ.· (e ℤ.· x))
                                            (ℤ.pos·pos (ℕ₊₁→ℕ d) (ℕ₊₁→ℕ f)) ∙
                                             assoc {a} {e})
                                       (sym (ℤ.·Assoc c e (ℕ₊₁→ℤ (b ·₊₁ f))) ∙
                                        cong (λ x → c ℤ.· (e ℤ.· x))
                                             (ℤ.pos·pos (ℕ₊₁→ℕ b) (ℕ₊₁→ℕ f)) ∙
                                              assoc {c} {e})
                                        aedf≤cebf))) }

  where assoc : ∀{a b c d} → a ℤ.· (b ℤ.· (c ℤ.· d)) ≡ a ℤ.· b ℤ.· c ℤ.· d
        assoc {a} {b} {c} {d} = cong (a ℤ.·_) (ℤ.·Assoc b c d) ∙
                                ℤ.·Assoc a (b ℤ.· c) d ∙
                                cong (ℤ._· d) (ℤ.·Assoc a b c)

<-·o : ∀ m n o → 0 < o → m < n → m ℚ.· o < n ℚ.· o
<-·o =
  elimProp3 {P = λ a b c → 0 < c → a < b → a ℚ.· c < b ℚ.· c}
            (λ x y z → isPropΠ2 λ _ _ → isProp< (x ℚ.· z) (y ℚ.· z))
             λ { (a , b) (c , d) (e , f) 0<e ad<cb
             → subst2 ℤ._<_ (cong (ℤ._· ℕ₊₁→ℤ f) (·CommR a (ℕ₊₁→ℤ d) e) ∙
                             sym (ℤ.·Assoc (a ℤ.· e) (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ f)) ∙
                             cong (a ℤ.· e ℤ.·_) (sym (ℤ.pos·pos (ℕ₊₁→ℕ d) (ℕ₊₁→ℕ f))))
                            (cong (ℤ._· ℕ₊₁→ℤ f) (·CommR c (ℕ₊₁→ℤ b) e) ∙
                             sym (ℤ.·Assoc (c ℤ.· e) (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ f)) ∙
                             cong (c ℤ.· e ℤ.·_) (sym (ℤ.pos·pos (ℕ₊₁→ℕ b) (ℕ₊₁→ℕ f))))
                            (ℤ.<-·o {k = -1+ f}
                                    (ℤ.0<o→<-·o (subst (0 ℤ.<_) (ℤ.·IdR e) 0<e) ad<cb)) }


<-o· : ∀ m n o → 0 < o → m < n → o ℚ.· m < o ℚ.· n
<-o· m n o x = subst2 _<_ (·Comm m o)
                         (·Comm n o) ∘
             <-·o m n o x


0<-m·n : ∀ m n → 0 < m → 0 < n → 0 < m ℚ.· n
0<-m·n m n x y = subst (_< (m ℚ.· n)) (ℚ.·AnnihilL n)
             (<-·o 0 m n y x)


<-·o-cancel : ∀ m n o → 0 < o → m ℚ.· o < n ℚ.· o → m < n
<-·o-cancel =
  elimProp3 {P = λ a b c → 0 < c → a ℚ.· c < b ℚ.· c → a < b}
            (λ x y _ → isPropΠ2 λ _ _ → isProp< x y)
             λ { (a , b) (c , d) (e , f) 0<e aedf<cebf
             → ℤ.0<o→<-·o-cancel (subst (0 ℤ.<_) (ℤ.·IdR e) 0<e)
               (subst2 ℤ._<_ (·CommR a e (ℕ₊₁→ℤ d)) (·CommR c e (ℕ₊₁→ℤ b))
                      (ℤ.<-·o-cancel {k = -1+ f}
                        (subst2 ℤ._<_ (sym (ℤ.·Assoc a e (ℕ₊₁→ℤ (d ·₊₁ f))) ∙
                                       cong (λ x → a ℤ.· (e ℤ.· x))
                                            (ℤ.pos·pos (ℕ₊₁→ℕ d) (ℕ₊₁→ℕ f)) ∙
                                             assoc {a} {e})
                                       (sym (ℤ.·Assoc c e (ℕ₊₁→ℤ (b ·₊₁ f))) ∙
                                        cong (λ x → c ℤ.· (e ℤ.· x))
                                             (ℤ.pos·pos (ℕ₊₁→ℕ b) (ℕ₊₁→ℕ f)) ∙
                                              assoc {c} {e})
                                        aedf<cebf))) }

  where assoc : ∀{a b c d} → a ℤ.· (b ℤ.· (c ℤ.· d)) ≡ a ℤ.· b ℤ.· c ℤ.· d
        assoc {a} {b} {c} {d} = cong (a ℤ.·_) (ℤ.·Assoc b c d) ∙
                                ℤ.·Assoc a (b ℤ.· c) d ∙
                                cong (ℤ._· d) (ℤ.·Assoc a b c)

min≤ : ∀ m n → ℚ.min m n ≤ m
min≤
    = elimProp2 {P = λ a b → ℚ.min a b ≤ a}
                (λ x y → isProp≤ (ℚ.min x y) x)
                 λ { (a , b) (c , d)
                  → subst2 ℤ._≤_ (sym (ℤ.·DistPosLMin (a ℤ.· ℕ₊₁→ℤ d)
                                                       (c ℤ.· ℕ₊₁→ℤ b)
                                                       (ℕ₊₁→ℕ b)))
                                  (sym (ℤ.·Assoc a (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b)) ∙
                                   cong (a ℤ.·_) (sym (ℤ.pos·pos (ℕ₊₁→ℕ d) (ℕ₊₁→ℕ b)) ∙
                                                  cong ℕ₊₁→ℤ (·₊₁-comm d b)))
                                  (ℤ.min≤ {a ℤ.· ℕ₊₁→ℤ d ℤ.· ℕ₊₁→ℤ b}
                                           {c ℤ.· ℕ₊₁→ℤ b ℤ.· ℕ₊₁→ℤ b}) }

min≤' : ∀ m n → ℚ.min m n ≤ n
min≤' m n = subst (_≤ n) (ℚ.minComm n m) (min≤ n m)

≤→min : ∀ m n → m ≤ n → ℚ.min m n ≡ m
≤→min
    = elimProp2 {P = λ a b → a ≤ b → ℚ.min a b ≡ a}
                (λ x y → isProp→ (isSetℚ (ℚ.min x y) x))
                 λ { (a , b) (c , d) ad≤cb
                  → eq/ (ℤ.min (a ℤ.· ℕ₊₁→ℤ d)
                               (c ℤ.· ℕ₊₁→ℤ b)
                         , b ·₊₁ d)
                        (a , b)
                        (cong (ℤ._· ℕ₊₁→ℤ b) (ℤ.≤→min ad≤cb) ∙
                         sym (ℤ.·Assoc a (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b)) ∙
                         cong (a ℤ.·_) (sym (ℤ.pos·pos (ℕ₊₁→ℕ d) (ℕ₊₁→ℕ b)) ∙
                                        cong ℕ₊₁→ℤ (·₊₁-comm d b))) }

≤max : ∀ m n → m ≤ ℚ.max m n
≤max
    = elimProp2 {P = λ a b → a ≤ ℚ.max a b}
                (λ x y → isProp≤ x (ℚ.max x y))
                 λ { (a , b) (c , d)
                  → subst2 ℤ._≤_ (sym (ℤ.·Assoc a (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b)) ∙
                                   cong (a ℤ.·_) (sym (ℤ.pos·pos (ℕ₊₁→ℕ d) (ℕ₊₁→ℕ b)) ∙
                                                  cong ℕ₊₁→ℤ (·₊₁-comm d b)))
                                  (sym (ℤ.·DistPosLMax (a ℤ.· ℕ₊₁→ℤ d)
                                                       (c ℤ.· ℕ₊₁→ℤ b)
                                                       (ℕ₊₁→ℕ b)))
                                  (ℤ.≤max {a ℤ.· ℕ₊₁→ℤ d ℤ.· ℕ₊₁→ℤ b}
                                           {c ℤ.· ℕ₊₁→ℤ b ℤ.· ℕ₊₁→ℤ b}) }
≤max' : ∀ m n → n ≤ ℚ.max m n
≤max' m n = subst (n ≤_) (ℚ.maxComm n m) (≤max n m)

≤→max : ∀ m n →  m ≤ n → ℚ.max m n ≡ n
≤→max m n
    = elimProp2 {P = λ a b → a ≤ b → ℚ.max a b ≡ b}
                (λ x y → isProp→ (isSetℚ (ℚ.max x y) y))
                (λ { (a , b) (c , d) ad≤cb
                  → eq/ (ℤ.max (a ℤ.· ℕ₊₁→ℤ d)
                               (c ℤ.· ℕ₊₁→ℤ b)
                         , b ·₊₁ d)
                        (c , d)
                        (cong (ℤ._· ℕ₊₁→ℤ d) (ℤ.≤→max ad≤cb) ∙
                         sym (ℤ.·Assoc c (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ d)) ∙
                         cong (c ℤ.·_) (sym (ℤ.pos·pos (ℕ₊₁→ℕ b) (ℕ₊₁→ℕ d)))) }) m n

≤Dec : ∀ m n → Dec (m ≤ n)
≤Dec = elimProp2 (λ x y → isPropDec (isProp≤ x y))
       λ { (a , b) (c , d) → ℤ.≤Dec (a ℤ.· ℕ₊₁→ℤ d) (c ℤ.· ℕ₊₁→ℤ b) }

<Dec : ∀ m n → Dec (m < n)
<Dec = elimProp2 (λ x y → isPropDec (isProp< x y))
       λ { (a , b) (c , d) → ℤ.<Dec (a ℤ.· ℕ₊₁→ℤ d) (c ℤ.· ℕ₊₁→ℤ b) }

_≟_ : (m n : ℚ) → Trichotomy m n
m ≟ n with discreteℚ m n
... | yes m≡n = eq m≡n
... | no m≢n with inequalityImplies# m n m≢n
...             | inl m<n = lt m<n
...             | inr n<m = gt n<m

≤MonotoneMin : ∀ m n o s → m ≤ n → o ≤ s → ℚ.min m o ≤ ℚ.min n s
≤MonotoneMin m n o s m≤n o≤s
  = subst (_≤ ℚ.min n s)
          (sym (ℚ.minAssoc n s (ℚ.min m o)) ∙
           cong (ℚ.min n) (ℚ.minAssoc s m o ∙
                           cong (λ a → ℚ.min a o) (ℚ.minComm s m) ∙
                                 sym (ℚ.minAssoc m s o)) ∙
                           ℚ.minAssoc n m (ℚ.min s o) ∙
           cong₂ ℚ.min (ℚ.minComm n m ∙ ≤→min m n m≤n)
                       (ℚ.minComm s o ∙ ≤→min o s o≤s))
           (min≤ (ℚ.min n s) (ℚ.min m o))

≤MonotoneMax : ∀ m n o s → m ≤ n → o ≤ s → ℚ.max m o ≤ ℚ.max n s
≤MonotoneMax m n o s m≤n o≤s
  = subst (ℚ.max m o ≤_)
          (sym (ℚ.maxAssoc m o (ℚ.max n s)) ∙
           cong (ℚ.max m) (ℚ.maxAssoc o n s ∙
                           cong (λ a → ℚ.max a s) (ℚ.maxComm o n) ∙
                                 sym (ℚ.maxAssoc n o s)) ∙
                           ℚ.maxAssoc m n (ℚ.max o s) ∙
           cong₂ ℚ.max (≤→max m n m≤n) (≤→max o s o≤s))
          (≤max (ℚ.max m o) (ℚ.max n s))



≡Weaken≤ : ∀ m n → m ≡ n → m ≤ n
≡Weaken≤ m n m≡n = subst (m ≤_) m≡n (isRefl≤ m)

≤→≯ : ∀ m n →  m ≤ n → ¬ (m > n)
≤→≯ m n m≤n n<m = isIrrefl< n (subst (n <_) (isAntisym≤ m n m≤n (<Weaken≤ n m n<m)) n<m)

≮→≥ : ∀ m n → ¬ (m < n) → m ≥ n
≮→≥ m n m≮n with discreteℚ m n
... | yes m≡n = ≡Weaken≤ n m (sym m≡n)
... | no  m≢n = ∥₁.elim (λ _ → isProp≤ n m)
                        (⊎.rec (⊥.rec ∘ m≮n) (<Weaken≤ n m))
                        (isConnected< m n m≢n)

0<+ : ∀ m n → 0 < m ℚ.+ n → (0 < m) ⊎ (0 < n)
0<+ m n 0<m+n with <Dec 0 m | <Dec 0 n
... | no 0≮m | no 0≮n = ⊥.rec (≤→≯ (m ℚ.+ n) 0 (≤Monotone+ m 0 n 0 (≮→≥ 0 m 0≮m) (≮→≥ 0 n 0≮n)) 0<m+n)
... | no _    | yes 0<n = inr 0<n
... | yes 0<m | _ = inl 0<m


minus-< : ∀ m n → m < n → - n < - m
minus-< m n p =
  let z = (<-+o m n (- (n ℚ.+ m)) p)
      p : m ℚ.+ ((- (n ℚ.+ m)))  ≡ - n
      p = cong (m ℚ.+_) (-Distr n m ∙ +Comm (- n) (- m)) ∙∙
             +Assoc m (- m) (- n) ∙∙
               ((cong (ℚ._+ - n) (+InvR m) ∙ +IdL (- n) ))
      q : n ℚ.+ ((- (n ℚ.+ m))) ≡ - m
      q = cong (n ℚ.+_) (-Distr n m) ∙∙ +Assoc n (- n) (- m) ∙∙
           (cong (ℚ._+ - m) (+InvR n) ∙ +IdL (- m) )
  in subst2 _<_ p q z



minus-≤ : ∀ m n → m ≤ n → - n ≤ - m
minus-≤ m n p =
  let z = (≤-+o m n (- (n ℚ.+ m)) p)
      p : m ℚ.+ ((- (n ℚ.+ m)))  ≡ - n
      p = cong (m ℚ.+_) (-Distr n m ∙ +Comm (- n) (- m)) ∙∙
             +Assoc m (- m) (- n) ∙∙
               ((cong (ℚ._+ - n) (+InvR m) ∙ +IdL (- n) ))
      q : n ℚ.+ ((- (n ℚ.+ m))) ≡ - m
      q = cong (n ℚ.+_) (-Distr n m) ∙∙ +Assoc n (- n) (- m) ∙∙
           (cong (ℚ._+ - m) (+InvR n) ∙ +IdL (- m) )
  in subst2 _≤_ p q z

<→<minus : ∀ m n → m < n → 0 < n - m
<→<minus m n x = subst (_< n - m) (+InvR m) (<-+o m n (- m) x)


minus-<' : ∀ n m → - n < - m → m < n
minus-<' n m p =
  subst2 _<_ (-Invol m) (-Invol n)
   (minus-< (ℚ.- n) (ℚ.- m) p)


0<ₚ_ : ℚ → hProp ℓ-zero
0<ₚ_ = Rec.go w
 where
 w : Rec (hProp ℓ-zero)
 w .Rec.isSetB = isSetHProp
 w .Rec.f (x , _) = ℤ.0< x , ℤ.isProp0< x
 w .Rec.f∼ (x , y) (x' , y') p =
  ⇔toPath --0<·ℕ₊₁
     (λ u → ℤ.0<·ℕ₊₁ x' y
       (subst ℤ.0<_ p (ℤ.·0< x (ℤ.pos (ℕ₊₁→ℕ y'))
         u _)))
     (λ u → ℤ.0<·ℕ₊₁ x y'
       (subst ℤ.0<_ (sym p) (ℤ.·0< x' (ℤ.pos (ℕ₊₁→ℕ y))
         u _)))

0<_ = fst ∘ 0<ₚ_


·0< : ∀ m n → 0< m → 0< n → 0< (m ℚ.· n)
·0< = elimProp2
  (λ x x' → isPropΠ2 λ _ _ → snd (0<ₚ (x ℚ.· x')) )
  λ (x , _) (x' , _) → ℤ.·0< x x'

+0< : ∀ m n → 0< m → 0< n → 0< (m ℚ.+ n)
+0< = elimProp2
  (λ x x' → isPropΠ2 λ _ _ → snd (0<ₚ (x ℚ.+ x')) )
  λ (x , y) (x' , y')  p p' →
    ℤ.+0< (x ℤ.· ℕ₊₁→ℤ y') (x' ℤ.· ℕ₊₁→ℤ y)
      (ℤ.·0< x (ℕ₊₁→ℤ y') p tt) (ℤ.·0< x' (ℕ₊₁→ℤ y) p' tt)

+0<' : ∀ m n o → 0< m → 0< n → (m ℚ.+ n) ≡ o → 0< o
+0<' m n o x y p = subst (0<_) p (+0< m n x y)

+₃0< : ∀ m n o → 0< m → 0< n → 0< o → 0< ((m ℚ.+ n) ℚ.+ o)
+₃0< m n o x y z = +0< (m ℚ.+ n) o (+0< m n x y) z

+₃0<' : ∀ m n o o' → 0< m → 0< n → 0< o
        → ((m ℚ.+ n) ℚ.+ o) ≡ o' → 0< o'
+₃0<' m n o o' x y z p = subst 0<_ p (+₃0< m n o x y z)


ℚ₊ : Type
ℚ₊ = Σ ℚ 0<_


instance
  fromNatℚ₊ : HasFromNat ℚ₊
  fromNatℚ₊ =
   record { Constraint = λ { zero → ⊥ ; _ → Unit }
             ; fromNat = λ { (suc n) → ([ ℤ.pos (suc n) , 1 ] , _) } }

ℚ₊≡ : {x y : ℚ₊} → fst x ≡ fst y → x ≡ y
ℚ₊≡ = Σ≡Prop (snd ∘ 0<ₚ_)

_ℚ₊·_ : ℚ₊ → ℚ₊ → ℚ₊
_ℚ₊·_ x x₁ = ((fst x) ℚ.· (fst x₁)) ,
  ·0< (fst x) (fst x₁) (snd x) (snd x₁)

_ℚ₊+_ : ℚ₊ → ℚ₊ → ℚ₊
_ℚ₊+_ x x₁ = ((fst x) ℚ.+ (fst x₁)) ,
  +0< (fst x) (fst x₁) (snd x) (snd x₁)

0<→< : ∀ q → 0< q → 0 < q
0<→< = elimProp (λ x → isProp→ (isProp< 0 x)) zz
 where

 zz : ∀ a → 0< [ a ] → 0 < [ a ]
 zz (ℤ.pos (suc n) , snd₁) x = n ,
  (sym (ℤ.pos+ 1 n) ∙ sym (ℤ.·IdR (ℤ.pos (suc n))))

0<ℚ₊ : (ε : ℚ₊) → 0 < fst ε
0<ℚ₊ = uncurry 0<→<

0≤ℚ₊ : (ε : ℚ₊) → 0 ≤ fst ε
0≤ℚ₊ ε = <Weaken≤ 0 (fst ε) (uncurry 0<→< ε)


<→0< : ∀ q → 0 < q → 0< q
<→0< = elimProp (λ x → isProp→ (snd (0<ₚ x)))
 zz
 where
 zz : ∀ a → 0 < [ a ] → 0< [ a ]
 zz (ℤ.pos zero , snd₁) x =
  ℕ.snotz (ℤ.injPos (ℤ.pos+ 1 (x .fst) ∙ snd x))
 zz (ℤ.pos (suc n) , snd₁) x = tt
 zz (ℤ.negsuc n , snd₁) x =
   ℤ.posNotnegsuc _ _
    (ℤ.pos+ 1 (x .fst) ∙  snd x ∙ ℤ.·IdR (ℤ.negsuc n))

0<-min : ∀ x y → 0< x → 0< y → 0< (ℚ.min x y)
0<-min = elimProp2
 (λ x y → isPropΠ2 λ _ _ → snd (0<ₚ (ℚ.min x y)))
 λ a b x x₁ →
   let zzz = ℤ.min-0< (a .fst ℤ.· ℕ₊₁→ℤ (b .snd)) (b .fst ℤ.· ℕ₊₁→ℤ (a .snd))
                (ℤ.·0< (a .fst) (ℕ₊₁→ℤ (b .snd)) x _ )
                 ((ℤ.·0< (b .fst) (ℕ₊₁→ℤ (a .snd)) x₁ _ ))

   in zzz

min₊ : ℚ₊ → ℚ₊ → ℚ₊
min₊ (x , y) (x' , y') =
  ℚ.min x x' , 0<-min x x' y y'

max₊ : ℚ₊ → ℚ₊ → ℚ₊
max₊ (x , y) (x' , y') =
  ℚ.max x x' , <→0< (ℚ.max x x') (isTrans<≤ 0 x _ (0<→< x y) (≤max x x'))

-- min< : ∀ n m → n < m →  ℚ.min n m ≡ n
-- min< = elimProp2 (λ _ _ → isPropΠ λ _ → isSetℚ _ _)
--   λ (x , y) (x' , y') →
--     {!!}
-- -- with n ≟ m
-- ... | lt x₁ = {!x!}
-- ... | eq x₁ = cong (ℚ.min n) (sym x₁) ∙ minIdem n
-- ... | gt x₁ = {!x!}

-< : ∀ q r → q < r → 0 < r ℚ.- q
-< q r x = subst (_< r ℚ.- q) (+InvR q) (<-+o q r (ℚ.- q) x)

-≤ : ∀ q r → q ≤ r → 0 ≤ r ℚ.- q
-≤ q r x = subst (_≤ r ℚ.- q) (+InvR q) (≤-+o q r (ℚ.- q) x)


<→ℚ₊ : ∀ x y → x < y → ℚ₊
<→ℚ₊ x y x<y = y - x , <→0< (y - x) (-< x y x<y)

<+ℚ₊ : ∀ x y (ε : ℚ₊) → x < y → x < (y ℚ.+ fst ε)
<+ℚ₊ x y ε x₁ =
 subst (_< y ℚ.+ fst ε)
   (ℚ.+IdR x) (<Monotone+ x y 0 (fst ε) x₁ (0<ℚ₊ ε))

<+ℚ₊' : ∀ x y (ε : ℚ₊) → x ≤ y → x < (y ℚ.+ fst ε)
<+ℚ₊' x y ε x₁ =
 subst (_< y ℚ.+ fst ε)
   (ℚ.+IdR x) (≤<Monotone+ x y 0 (fst ε) x₁ (0<ℚ₊ ε))


≤+ℚ₊ : ∀ x y (ε : ℚ₊) → x ≤ y → x ≤ (y ℚ.+ fst ε)
≤+ℚ₊ x y ε x₁ =
 subst (_≤ y ℚ.+ fst ε)
   (ℚ.+IdR x) (≤Monotone+ x y 0 (fst ε) x₁ (0≤ℚ₊ ε))


-ℚ₊<0 : (ε : ℚ₊) → ℚ.- (fst ε) < 0
-ℚ₊<0 ε = minus-< 0 (fst ε) (0<ℚ₊ ε)

-ℚ₊≤0 : (ε : ℚ₊) → ℚ.- (fst ε) ≤ 0
-ℚ₊≤0 ε = <Weaken≤ (ℚ.- (fst ε)) 0 (minus-< 0 (fst ε) (0<ℚ₊ ε))

pos[-x<x] : (ε : ℚ₊) → ℚ.- (fst ε) < (fst ε)
pos[-x<x] ε = isTrans< (ℚ.- (fst ε)) 0 (fst ε) (-ℚ₊<0 ε) (0<ℚ₊ ε)

pos[-x≤x] : (ε : ℚ₊) → ℚ.- (fst ε) ≤ (fst ε)
pos[-x≤x] ε = isTrans≤ (ℚ.- (fst ε)) 0 (fst ε) (-ℚ₊≤0 ε) (0≤ℚ₊ ε)

<-ℚ₊ : ∀ x y (ε : ℚ₊) → x < y → (x ℚ.- fst ε) < y
<-ℚ₊ x y ε x₁ =
 subst ((x ℚ.- fst ε) <_)
   (ℚ.+IdR y) (<Monotone+ x y (ℚ.- (fst ε)) 0 x₁ (-ℚ₊<0 ε))


<-ℚ₊' : ∀ x y (ε : ℚ₊) → x ≤ y → (x ℚ.- fst ε) < y
<-ℚ₊' x y ε x₁ =
 subst ((x ℚ.- fst ε) <_)
   (ℚ.+IdR y) (≤<Monotone+ x y (ℚ.- (fst ε)) 0 x₁ (-ℚ₊<0 ε))


≤-ℚ₊ : ∀ x y (ε : ℚ₊) → x ≤ y → (x ℚ.- fst ε) ≤ y
≤-ℚ₊ x y ε x₁ =
 subst ((x ℚ.- fst ε) ≤_)
   (ℚ.+IdR y) (≤Monotone+ x y (ℚ.- (fst ε)) 0 x₁ (-ℚ₊≤0 ε))

-ℚ₊<ℚ₊ : (ε ε' : ℚ₊) → (ℚ.- (fst ε)) < fst ε'
-ℚ₊<ℚ₊ ε ε' = isTrans< (ℚ.- (fst ε)) 0 (fst ε') (-ℚ₊<0 ε) (0<ℚ₊ ε')

-ℚ₊≤ℚ₊ : (ε ε' : ℚ₊) → ℚ.- (fst ε) ≤ fst ε'
-ℚ₊≤ℚ₊ ε ε' = isTrans≤ (ℚ.- fst ε) 0 (fst ε') (-ℚ₊≤0 ε) (0≤ℚ₊ ε')


absCases : (q : ℚ) → (abs q ≡ - q) ⊎ (abs q ≡ q)
absCases q with (- q) ≟ q
... | lt x = inr (ℚ.maxComm q (- q) ∙ (≤→max (- q) q $ <Weaken≤ (- q) q x))
... | eq x = inr (ℚ.maxComm q (- q) ∙ (≤→max (- q) q $ ≡Weaken≤ (- q) q x))
... | gt x = inl (≤→max q (- q) (<Weaken≤ q (- q) x) )


absFrom≤×≤ : ∀ ε q →
                - ε ≤ q
                → q ≤ ε
                → abs q ≤ ε
absFrom≤×≤ ε q x x₁ with absCases q
... | inl x₂ = subst2 (_≤_) (sym x₂) (-Invol ε) (minus-≤ (- ε) q x  )
... | inr x₂ = subst (_≤ ε) (sym x₂) x₁

absFrom<×< : ∀ ε q →
                - ε < q
                → q < ε
                → abs q < ε
absFrom<×< ε q x x₁ with absCases q
... | inl x₂ = subst2 (_<_) (sym x₂) (-Invol ε) (minus-< (- ε) q x  )
... | inr x₂ = subst (_< ε) (sym x₂) x₁


clamp : ℚ → ℚ → ℚ → ℚ
clamp d u x = ℚ.min (ℚ.max d x) u

≠→0<abs : ∀ q r → ¬ q ≡ r → 0< ℚ.abs (q ℚ.- r)
≠→0<abs q r u with q ≟ r
... | lt x = <→0< (ℚ.abs (q ℚ.- r)) $ isTrans<≤ 0 (r ℚ.- q) (ℚ.abs (q ℚ.- r))
                 (-< q r x)
                   (subst (_≤ abs (q - r))
                     (-[x-y]≡y-x q r) $ ≤max' (q - r) (ℚ.- (q - r)))
... | eq x = ⊥.rec (u x)
... | gt x = <→0< (ℚ.abs (q ℚ.- r)) $ isTrans<≤ 0 (q ℚ.- r) (ℚ.abs (q ℚ.- r))
                 (-< r q x) (≤max (q - r) (ℚ.- (q - r)))

≤→≡⊎< : ∀ q r → q ≤ r → (q ≡ r) ⊎ (q < r)
≤→≡⊎< q r y with q ≟ r
... | lt x = inr x
... | eq x = inl x
... | gt x = ⊥.rec (≤→≯ q r y x)

≤ℤ→≤ℚ : ∀ m n → m ℤ.≤ n → [ m , 1 ] ≤ [ n , 1 ]
≤ℤ→≤ℚ m n = subst2 ℤ._≤_ (sym (ℤ.·IdR m)) (sym (ℤ.·IdR n))

<ℤ→<ℚ : ∀ m n → m ℤ.< n → [ m , 1 ] < [ n , 1 ]
<ℤ→<ℚ m n = subst2 ℤ._<_ (sym (ℤ.·IdR m)) (sym (ℤ.·IdR n))

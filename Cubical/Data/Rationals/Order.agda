module Cubical.Data.Rationals.Order where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence

open import Cubical.Functions.Logic using (_⊔′_; ⇔toPath)
open import Cubical.Foundations.Powerset

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Fast.Int.Base as ℤ using (ℤ; ℕ₊₁→ℤ)
import Cubical.Data.Fast.Int.Properties as ℤ
import Cubical.Data.Fast.Int.Order as ℤ
open import Cubical.Data.Fast.Int.Divisibility as ℤ
open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Data.Rationals.Properties as ℚ
open import Cubical.Data.Nat as ℕ
open import Cubical.Data.List using (List;[];_∷_)
open import Cubical.Data.Bool using (Bool;true;false;if_then_else_)
open import Cubical.Data.Nat.Mod as ℕ
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎ using (_⊎_; inl; inr; isProp⊎)

open import Cubical.HITs.PropositionalTruncation as ∥₁ using (isPropPropTrunc; ∣_∣₁)
open import Cubical.HITs.SetQuotients

open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary.Base
open import Cubical.Tactics.CommRingSolver

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
        lemma≤ (a , b) (c , d) (e , f) cf≡ed =
          (ua (propBiimpl→Equiv
            (ℤ.isProp≤ {a ℤ.· ℕ₊₁→ℤ d} {c ℤ.· ℕ₊₁→ℤ b})
            (ℤ.isProp≤ {a ℤ.· ℕ₊₁→ℤ f} {e ℤ.· ℕ₊₁→ℤ b})
                (ℤ.≤-·o-cancel {a ℤ.· ℕ₊₁→ℤ f} {k = -1+ d} ∘
                  subst2 ℤ._≤_ (·CommR a (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ f))
                               (·CommR c (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ f) ∙
                                cong (ℤ._· ℕ₊₁→ℤ b) cf≡ed ∙
                                ·CommR e (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b)) ∘
                 ℤ.≤-·o {a ℤ.· ℕ₊₁→ℤ d} {k = ℕ₊₁→ℕ f})
                (ℤ.≤-·o-cancel {a ℤ.· ℕ₊₁→ℤ d} {k = -1+ f} ∘
                  subst2 ℤ._≤_ (·CommR a (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ d))
                                (·CommR e (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ d) ∙
                                 cong (ℤ._· ℕ₊₁→ℤ b) (sym cf≡ed) ∙
                                 ·CommR c (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ b)) ∘
                 ℤ.≤-·o {a ℤ.· ℕ₊₁→ℤ f} {k = ℕ₊₁→ℕ d})))

        fun₀ : ℤ × ℕ₊₁ → ℚ → hProp ℓ-zero
        fst (fun₀ (a , b) [ c , d ]) = a ℤ.· ℕ₊₁→ℤ d ℤ.≤ c ℤ.· ℕ₊₁→ℤ b
        snd (fun₀ (a , b) [ c , d ]) = ℤ.isProp≤ {a ℤ.· ℕ₊₁→ℤ d} {c ℤ.· ℕ₊₁→ℤ b}
        fun₀ a/b (eq/ c/d e/f cf≡ed i) = record
          { fst = lemma≤ a/b c/d e/f cf≡ed i
          ; snd = isProp→PathP (λ i → isPropIsProp {A = lemma≤ a/b c/d e/f cf≡ed i})
            (ℤ.isProp≤ {a/b .fst ℤ.· ℕ₊₁→ℤ (c/d .snd)} {c/d .fst ℤ.· ℕ₊₁→ℤ (a/b .snd)})
            (ℤ.isProp≤ {a/b .fst ℤ.· ℕ₊₁→ℤ (e/f .snd)} {e/f .fst ℤ.· ℕ₊₁→ℤ (a/b .snd)})
            i
          }
        fun₀ a/b (squash/ x y p q i j) = isSet→SquareP (λ _ _ → isSetHProp)
          (λ _ → fun₀ a/b x)
          (λ _ → fun₀ a/b y)
          (λ i → fun₀ a/b (p i))
          (λ i → fun₀ a/b (q i)) j i

        toPath : ∀ a/b c/d (x : a/b ∼ c/d) (y : ℚ) → fun₀ a/b y ≡ fun₀ c/d y
        toPath (a , b) (c , d) ad≡cb = elimProp (λ _ → isSetHProp _ _) λ (e , f) →
          Σ≡Prop (λ _ → isPropIsProp) (ua (propBiimpl→Equiv
            (ℤ.isProp≤ {a ℤ.· ℕ₊₁→ℤ f} {e ℤ.· ℕ₊₁→ℤ b})
            (ℤ.isProp≤ {c ℤ.· ℕ₊₁→ℤ f} {e ℤ.· ℕ₊₁→ℤ d})
                (ℤ.≤-·o-cancel {c ℤ.· ℕ₊₁→ℤ f} {k = -1+ b} ∘
                  subst2 ℤ._≤_ (·CommR a (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ d) ∙
                                 cong (ℤ._· ℕ₊₁→ℤ f) ad≡cb ∙
                                 ·CommR c (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ f))
                               (·CommR e (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ d)) ∘
                 ℤ.≤-·o {a ℤ.· ℕ₊₁→ℤ f} {k = ℕ₊₁→ℕ d})
                (ℤ.≤-·o-cancel {a ℤ.· ℕ₊₁→ℤ f} {k = -1+ d} ∘
                  subst2 ℤ._≤_ (·CommR c (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ b) ∙
                                 cong (ℤ._· ℕ₊₁→ℤ f) (sym ad≡cb) ∙
                                 ·CommR a (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ f))
                               (·CommR e (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b)) ∘
                 ℤ.≤-·o {c ℤ.· ℕ₊₁→ℤ f} {k = ℕ₊₁→ℕ b})))

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
        lemma< (a , b) (c , d) (e , f) cf≡ed =
          ua (propBiimpl→Equiv
            (ℤ.isProp< {a ℤ.· ℕ₊₁→ℤ d} {c ℤ.· ℕ₊₁→ℤ b})
            (ℤ.isProp< {a ℤ.· ℕ₊₁→ℤ f} {e ℤ.· ℕ₊₁→ℤ b})
                (ℤ.<-·o-cancel {a ℤ.· ℕ₊₁→ℤ f} {k = -1+ d} ∘
                  subst2 ℤ._<_ (·CommR a (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ f))
                               (·CommR c (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ f) ∙
                                cong (ℤ._· ℕ₊₁→ℤ b) cf≡ed ∙
                                ·CommR e (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b)) ∘
                 ℤ.<-·o {a ℤ.· ℕ₊₁→ℤ d} {k = -1+ f})
                (ℤ.<-·o-cancel {a ℤ.· ℕ₊₁→ℤ d} {k = -1+ f} ∘
                  subst2 ℤ._<_ (·CommR a (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ d))
                               (·CommR e (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ d) ∙
                                cong (ℤ._· ℕ₊₁→ℤ b) (sym cf≡ed) ∙
                                ·CommR c (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ b)) ∘
                 ℤ.<-·o {a ℤ.· ℕ₊₁→ℤ f} {k = -1+ d}))

        fun₀ : ℤ × ℕ₊₁ → ℚ → hProp ℓ-zero
        fst (fun₀ (a , b) [ c , d ]) = a ℤ.· ℕ₊₁→ℤ d ℤ.< c ℤ.· ℕ₊₁→ℤ b
        snd (fun₀ (a , b) [ c , d ]) = ℤ.isProp< {a ℤ.· ℕ₊₁→ℤ d} {c ℤ.· ℕ₊₁→ℤ b}
        fun₀ a/b (eq/ c/d e/f cf≡ed i) = record
          { fst = lemma< a/b c/d e/f cf≡ed i
          ; snd = isProp→PathP (λ i → isPropIsProp {A = lemma< a/b c/d e/f cf≡ed i})
            (ℤ.isProp< {a/b .fst ℤ.· ℕ₊₁→ℤ (c/d .snd)} {c/d .fst ℤ.· ℕ₊₁→ℤ (a/b .snd)})
            (ℤ.isProp< {a/b .fst ℤ.· ℕ₊₁→ℤ (e/f .snd)} {e/f .fst ℤ.· ℕ₊₁→ℤ (a/b .snd)})
            i
          }
        fun₀ a/b (squash/ x y p q i j) = isSet→SquareP (λ _ _ → isSetHProp)
          (λ _ → fun₀ a/b x)
          (λ _ → fun₀ a/b y)
          (λ i → fun₀ a/b (p i))
          (λ i → fun₀ a/b (q i)) j i

        toPath : ∀ a/b c/d (x : a/b ∼ c/d) (y : ℚ) → fun₀ a/b y ≡ fun₀ c/d y
        toPath (a , b) (c , d) ad≡cb = elimProp (λ _ → isSetHProp _ _) λ (e , f) →
          Σ≡Prop (λ _ → isPropIsProp) (ua (propBiimpl→Equiv
            (ℤ.isProp< {a ℤ.· ℕ₊₁→ℤ f} {e ℤ.· ℕ₊₁→ℤ b})
            (ℤ.isProp< {c ℤ.· ℕ₊₁→ℤ f} {e ℤ.· ℕ₊₁→ℤ d})
                (ℤ.<-·o-cancel {c ℤ.· ℕ₊₁→ℤ f} {k = -1+ b} ∘
                  subst2 ℤ._<_ (·CommR a (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ d) ∙
                                cong (ℤ._· ℕ₊₁→ℤ f) ad≡cb ∙
                                ·CommR c (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ f))
                               (·CommR e (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ d)) ∘
                 ℤ.<-·o {a ℤ.· ℕ₊₁→ℤ f} {k = -1+ d})
                (ℤ.<-·o-cancel {a ℤ.· ℕ₊₁→ℤ f} {k = -1+ d} ∘
                  subst2 ℤ._<_ (·CommR c (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ b) ∙
                                cong (ℤ._· ℕ₊₁→ℤ f) (sym ad≡cb) ∙
                                ·CommR a (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ f))
                               (·CommR e (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b)) ∘
                 ℤ.<-·o {c ℤ.· ℕ₊₁→ℤ f} {k = -1+ b})))

        fun : ℚ → ℚ → hProp ℓ-zero
        fun [ a/b ] y = fun₀ a/b y
        fun (eq/ a/b c/d ad≡cb i) y = toPath a/b c/d ad≡cb y i
        fun (squash/ x y p q i j) z = isSet→SquareP (λ _ _ → isSetHProp)
          (λ _ → fun x z) (λ _ → fun y z) (λ i → fun (p i) z) (λ i → fun (q i) z) j i

record _≤_ (m n : ℚ ) : Type₀ where
 constructor inj
 field
  prf : fst (m ≤' n)

record _<_ (m n : ℚ ) : Type₀ where
 constructor inj
 field
  prf : fst (m <' n)

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

record TrichotomyRec {ℓ : Level} (n : ℚ) (P : ℚ → Type ℓ) : Type ℓ where
  no-eta-equality
  field
    lt-case : ∀ m → (p : m < n) → P m
    eq-case : P n
    gt-case : ∀ m → (p : m > n) → P m

  go : ∀ m → (t : Trichotomy m n) → P m
  go m (lt p) = lt-case m p
  go m (eq p) = subst P (sym p) eq-case
  go m (gt p) = gt-case m p


module _ where
  open BinaryRelation

  isProp≤ : isPropValued _≤_
  isProp≤ m n (inj prf) (inj prf₁) = cong inj (snd (m ≤' n) prf prf₁)

  isProp< : isPropValued _<_
  isProp< m n (inj prf) (inj prf₁) = cong inj (snd (m <' n) prf prf₁)

  isRefl≤ : isRefl _≤_
  isRefl≤ = elimProp {P = λ x → x ≤ x} (λ x → isProp≤ x x) λ _ → inj ℤ.isRefl≤

  isIrrefl< : isIrrefl _<_
  isIrrefl< = elimProp {P = λ x → ¬ x < x} (λ _ → isProp¬ _) λ _ → ℤ.isIrrefl< ∘ _<_.prf

  isAntisym≤ : isAntisym _≤_
  isAntisym≤ =
    elimProp2 {P = λ a b → a ≤ b → b ≤ a → a ≡ b}
              (λ x y → isPropΠ2 λ _ _ → isSetℚ x y)
              λ a b (inj a≤b) (inj b≤a) → eq/ a b (ℤ.isAntisym≤ a≤b b≤a)

  isTrans≤ : isTrans _≤_
  isTrans≤ =
    elimProp3 {P = λ a b c → a ≤ b → b ≤ c → a ≤ c}
              (λ x _ z → isPropΠ2 λ _ _ → isProp≤ x z)
              λ (a , b) (c , d) (e , f) (inj ad≤cb) (inj cf≤ed) →
                inj (ℤ.≤-·o-cancel {a ℤ.· ℕ₊₁→ℤ f} {k = -1+ d}
                  (subst (ℤ._≤ e ℤ.· ℕ₊₁→ℤ b ℤ.· ℕ₊₁→ℤ d)
                    (·CommR a (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ f))
                  (ℤ.isTrans≤ {(a ℤ.· ℕ₊₁→ℤ d) ℤ.· ℕ₊₁→ℤ f}
                    (ℤ.≤-·o {a ℤ.· ℕ₊₁→ℤ d} {k = ℕ₊₁→ℕ f} ad≤cb)
                    (subst2 ℤ._≤_
                      (·CommR c (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ b))
                      (·CommR e (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b))
                      (ℤ.≤-·o {c ℤ.· ℕ₊₁→ℤ f} {k = ℕ₊₁→ℕ b} cf≤ed)))))

  isTrans< : isTrans _<_
  isTrans< =
    elimProp3 {P = λ a b c → a < b → b < c → a < c}
              (λ x _ z → isPropΠ2 λ _ _ → isProp< x z)
              λ { (a , b) (c , d) (e , f) (inj ad<cb) (inj cf<ed) →
                inj ( ℤ.<-·o-cancel {a ℤ.· ℕ₊₁→ℤ f} {k = -1+ d}
                  (subst (ℤ._< e ℤ.· ℕ₊₁→ℤ b ℤ.· ℕ₊₁→ℤ d)
                    (·CommR a (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ f))
                  (ℤ.isTrans< {(a ℤ.· ℕ₊₁→ℤ d) ℤ.· ℕ₊₁→ℤ f}
                    (ℤ.<-·o {a ℤ.· ℕ₊₁→ℤ d} {k = -1+ f} ad<cb)
                    (subst2 ℤ._<_
                      (·CommR c (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ b))
                      (·CommR e (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b))
                      (ℤ.<-·o {c ℤ.· ℕ₊₁→ℤ f} {k = -1+ b} cf<ed))))) }

  isAsym< : isAsym _<_
  isAsym< = isIrrefl×isTrans→isAsym _<_ (isIrrefl< , isTrans<)

  isTotal≤ : isTotal _≤_
  isTotal≤ =
    elimProp2 {P = λ a b → (a ≤ b) ⊔′ (b ≤ a)}
              (λ _ _ → isPropPropTrunc)
               λ a b → ∣ lem a b ∣₁
    where
      lem : (a b : ℤ.ℤ × ℕ₊₁) → ([ a ] ≤ [ b ]) ⊎ ([ b ] ≤ [ a ])
      lem (a , b) (c , d) with (a ℤ.· ℕ₊₁→ℤ d) ℤ.≟ (c ℤ.· ℕ₊₁→ℤ b)
      ... | ℤ.lt ad<cb = inl (inj (ℤ.<-weaken {a ℤ.· ℕ₊₁→ℤ d} ad<cb))
      ... | ℤ.eq ad≡cb = inl (inj (ℤ.Σℕ→≤ (0 , ℤ.+IdR _ ∙ ad≡cb)))
      ... | ℤ.gt cb<ad = inr (inj (ℤ.<-weaken {c ℤ.· ℕ₊₁→ℤ b} cb<ad))

  isConnected< : isConnected _<_
  isConnected< =
    elimProp2 {P = λ a b → (¬ a < b) × (¬ b < a) → a ≡ b}
              (λ a b → isProp→ (isSetℚ a b))
               lem
    where
      lem : (a b : ℤ.ℤ × ℕ₊₁) → (¬ [ a ] < [ b ]) × (¬ [ b ] < [ a ]) → [ a ] ≡ [ b ]
      lem (a , b) (c , d) (¬ad<cb , ¬cb<ad) with (a ℤ.· ℕ₊₁→ℤ d) ℤ.≟ (c ℤ.· ℕ₊₁→ℤ b)
      ... | ℤ.lt ad<cb = ⊥.rec (¬ad<cb (inj ad<cb))
      ... | ℤ.eq ad≡cb = eq/ (a , b) (c , d) ad≡cb
      ... | ℤ.gt cb<ad = ⊥.rec (¬cb<ad (inj cb<ad))

  isProp# : isPropValued _#_
  isProp# x y = isProp⊎ (isProp< x y) (isProp< y x) (isAsym< x y)

  isIrrefl# : isIrrefl _#_
  isIrrefl# x (inl x<x) = isIrrefl< x x<x
  isIrrefl# x (inr x<x) = isIrrefl< x x<x

  isSym# : isSym _#_
  isSym# _ _ (inl x<y) = inr x<y
  isSym# _ _ (inr y<x) = inl y<x

  inequalityImplies# : inequalityImplies _#_
  inequalityImplies#
    = elimProp2 {P = λ a b → ¬ a ≡ b → a # b}
                (λ a b → isProp→ (isProp# a b))
                 lem
    where
      lem : (a b : ℤ.ℤ × ℕ₊₁) → ¬ [_] {R = _∼_} a ≡ [ b ] → [ a ] # [ b ]
      lem (a , b) (c , d) ¬a≡b with (a ℤ.· ℕ₊₁→ℤ d) ℤ.≟ (c ℤ.· ℕ₊₁→ℤ b)
      ... | ℤ.lt ad<cb = inl (inj ad<cb)
      ... | ℤ.eq ad≡cb = ⊥.rec (¬a≡b (eq/ (a , b) (c , d) ad≡cb))
      ... | ℤ.gt cb<ad = inr (inj cb<ad)

  isWeaklyLinear< : isWeaklyLinear _<_
  isWeaklyLinear< =
    elimProp3 {P = λ a b c → a < b → (a < c) ⊔′ (c < b)}
              (λ _ _ _ → isProp→ isPropPropTrunc)
               lem
    where
      lem : (a b c : ℤ.ℤ × ℕ₊₁) → [ a ] < [ b ] → ([ a ] < [ c ]) ⊔′ ([ c ] < [ b ])
      lem a b c a<b with discreteℚ [ a ] [ c ]
      ... | yes a≡c = ∣ inr (subst (_< [ b ]) a≡c a<b) ∣₁
      ... | no a≢c = ∣ ⊎.map (λ a<c → a<c)
                             (λ c<a → isTrans< [ c ] [ a ] [ b ] c<a a<b)
                             (inequalityImplies# [ a ] [ c ] a≢c) ∣₁

  isCotrans# : isCotrans _#_
  isCotrans#
    = elimProp3 {P = λ a b c → a # b → (a # c) ⊔′ (b # c)}
                (λ _ _ _ → isProp→ isPropPropTrunc)
                 lem
      where
        lem : (a b c : ℤ.ℤ × ℕ₊₁) → [ a ] # [ b ] → ([ a ] # [ c ]) ⊔′ ([ b ] # [ c ])
        lem a b c a#b with discreteℚ [ b ] [ c ]
        ... | yes b≡c = ∣ inl (subst ([ a ] #_) b≡c a#b) ∣₁
        ... | no  b≢c = ∣ inr (inequalityImplies# [ b ] [ c ] b≢c) ∣₁

≤-+o : ∀ m n o → m ≤ n → m ℚ.+ o ≤ n ℚ.+ o
≤-+o =
  elimProp3 {P = λ a b c → a ≤ b → a ℚ.+ c ≤ b ℚ.+ c}
            (λ x y z → isProp→ (isProp≤ (x ℚ.+ z) (y ℚ.+ z)))
             λ { (a , b) (c , d) (e , f) ad≤cb → inj
               (subst2 {x = a ℤ.· ℕ₊₁→ℤ d ℤ.· ℤ.pos (ℕ₊₁→ℕ f ℕ.· ℕ₊₁→ℕ f) ℤ.+
                            e ℤ.· ℕ₊₁→ℤ b ℤ.· ℕ₊₁→ℤ d ℤ.· ℕ₊₁→ℤ f}
                       {y = (a ℤ.· ℕ₊₁→ℤ f ℤ.+ e ℤ.· ℕ₊₁→ℤ b) ℤ.· ℕ₊₁→ℤ (d ·₊₁ f)}
                        {z = c ℤ.· ℕ₊₁→ℤ b ℤ.· ℤ.pos (ℕ₊₁→ℕ f ℕ.· ℕ₊₁→ℕ f) ℤ.+
                              e ℤ.· ℕ₊₁→ℤ b ℤ.· ℕ₊₁→ℤ d ℤ.· ℕ₊₁→ℤ f}
                              {w = (c ℤ.· ℕ₊₁→ℤ f ℤ.+ e ℤ.· ℕ₊₁→ℤ d) ℤ.· ℕ₊₁→ℤ (b ·₊₁ f)}
                              ℤ._≤_
                       ℤ! ℤ!
                       (ℤ.≤-+o {a ℤ.· ℕ₊₁→ℤ d ℤ.· ℤ.pos (ℕ₊₁→ℕ f ℕ.· ℕ₊₁→ℕ f)}
                               {o = e ℤ.· ℕ₊₁→ℤ b ℤ.· ℕ₊₁→ℤ d ℤ.· ℕ₊₁→ℤ f}
                               (ℤ.≤-·o {a ℤ.· ℕ₊₁→ℤ d} {k = ℕ₊₁→ℕ (f ·₊₁ f)} (ad≤cb ._≤_.prf)))) }

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
               inj (subst2 {x = a ℤ.· ℕ₊₁→ℤ d ℤ.· ℤ.pos (ℕ₊₁→ℕ f ℕ.· ℕ₊₁→ℕ f) ℤ.+
                            e ℤ.· ℕ₊₁→ℤ b ℤ.· ℕ₊₁→ℤ d ℤ.· ℕ₊₁→ℤ f}
                      {y = (a ℤ.· ℕ₊₁→ℤ f ℤ.+ e ℤ.· ℕ₊₁→ℤ b) ℤ.· ℕ₊₁→ℤ (d ·₊₁ f)}
                      {z = c ℤ.· ℕ₊₁→ℤ b ℤ.· ℤ.pos (ℕ₊₁→ℕ f ℕ.· ℕ₊₁→ℕ f) ℤ.+
                            e ℤ.· ℕ₊₁→ℤ b ℤ.· ℕ₊₁→ℤ d ℤ.· ℕ₊₁→ℤ f}
                      {w = (c ℤ.· ℕ₊₁→ℤ f ℤ.+ e ℤ.· ℕ₊₁→ℤ d) ℤ.· ℕ₊₁→ℤ (b ·₊₁ f)}
                    ℤ._<_ ℤ! ℤ!
                       (ℤ.<-+o {a ℤ.· ℕ₊₁→ℤ d ℤ.· ℤ.pos (ℕ₊₁→ℕ f ℕ.· ℕ₊₁→ℕ f)}
                               {o = e ℤ.· ℕ₊₁→ℤ b ℤ.· ℕ₊₁→ℤ d ℤ.· ℕ₊₁→ℤ f}
                               (ℤ.<-·o {a ℤ.· ℕ₊₁→ℤ d} {k = -1+ (f ·₊₁ f)} (ad<cb ._<_.prf)))) }

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
                             (λ { (a , b) (c , d) →  inj ∘S (ℤ.<-weaken {a ℤ.· ℕ₊₁→ℤ d}) ∘ _<_.prf })
                                m n

isTrans<≤ : ∀ m n o → m < n → n ≤ o → m < o
isTrans<≤ =
    elimProp3 {P = λ a b c → a < b → b ≤ c → a < c}
              (λ x _ z → isPropΠ2 λ _ _ → isProp< x z)
               λ { (a , b) (c , d) (e , f) ad<cb cf≤ed
                → inj (ℤ.<-·o-cancel {a ℤ.· ℕ₊₁→ℤ f} {k = -1+ d}
                 (ℤ.<≤-trans {a ℤ.· ℕ₊₁→ℤ f ℤ.· ℕ₊₁→ℤ d} {m = c ℤ.· ℕ₊₁→ℤ f ℤ.· ℕ₊₁→ℤ b}
                              (subst2 ℤ._<_ (·CommR a (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ f))
                                            (·CommR c (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ f))
                                            (ℤ.<-·o {a ℤ.· ℕ₊₁→ℤ d} {k = -1+ f} (ad<cb ._<_.prf)))
                              (subst (c ℤ.· ℕ₊₁→ℤ f ℤ.· ℕ₊₁→ℤ b ℤ.≤_)
                                     (·CommR e (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b))
                                     (ℤ.≤-·o {c ℤ.· ℕ₊₁→ℤ f} {k = ℕ₊₁→ℕ b} (cf≤ed ._≤_.prf))) ))}

isTrans≤< : ∀ m n o → m ≤ n → n < o → m < o
isTrans≤< =
    elimProp3 {P = λ a b c → a ≤ b → b < c → a < c}
              (λ x _ z → isPropΠ2 λ _ _ → isProp< x z)
               λ { (a , b) (c , d) (e , f) ad≤cb cf<ed
                → inj (ℤ.<-·o-cancel {a ℤ.· ℕ₊₁→ℤ f} {k = -1+ d}
                 (ℤ.≤<-trans {a ℤ.· ℕ₊₁→ℤ f ℤ.· ℕ₊₁→ℤ d} {m = c ℤ.· ℕ₊₁→ℤ f ℤ.· ℕ₊₁→ℤ b}
                              (subst2 ℤ._≤_ (·CommR a (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ f))
                                             (·CommR c (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ f))
                                             (ℤ.≤-·o {a ℤ.· ℕ₊₁→ℤ d} {k = ℕ₊₁→ℕ f} (ad≤cb ._≤_.prf)))
                              (subst (c ℤ.· ℕ₊₁→ℤ f ℤ.· ℕ₊₁→ℤ b ℤ.<_)
                                     (·CommR e (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b))
                                     (ℤ.<-·o {c ℤ.· ℕ₊₁→ℤ f} {k = -1+ b} (cf<ed ._<_.prf))) ))}

<≤Monotone+ : ∀ m n o s → m < n → o ≤ s → m ℚ.+ o < n ℚ.+ s
<≤Monotone+ m n o s x x₁ =
   isTrans<≤ _ _ _ (<-+o m n o x) (≤-o+ o s n x₁)

≤<Monotone+ : ∀ m n o s → m ≤ n → o < s → m ℚ.+ o < n ℚ.+ s
≤<Monotone+ m n o s x x₁ =
   isTrans≤< _ _ _ (≤-+o m n o x) (<-o+ o s n x₁)


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
             → inj (subst2 ℤ._≤_ (cong (ℤ._· ℕ₊₁→ℤ f) (·CommR a (ℕ₊₁→ℤ d) e) ∙
                              sym (ℤ.·Assoc (a ℤ.· e) (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ f)) ∙
                              cong (a ℤ.· e ℤ.·_) (sym (ℤ.pos·pos (ℕ₊₁→ℕ d) (ℕ₊₁→ℕ f))))
                             (cong (ℤ._· ℕ₊₁→ℤ f) (·CommR c (ℕ₊₁→ℤ b) e) ∙
                              sym (ℤ.·Assoc (c ℤ.· e) (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ f)) ∙
                              cong (c ℤ.· e ℤ.·_) (sym (ℤ.pos·pos (ℕ₊₁→ℕ b) (ℕ₊₁→ℕ f))))
                             (ℤ.≤-·o {a ℤ.· ℕ₊₁→ℤ d ℤ.· e} {k = ℕ₊₁→ℕ f}
                                    (ℤ.0≤o→≤-·o {e} {a ℤ.· ℕ₊₁→ℤ d}
                                    (subst (0 ℤ.≤_) (ℤ.·IdR e) (0≤e ._≤_.prf)) (ad≤cb ._≤_.prf)))) }

≤-o· : ∀ m n o → 0 ≤ o → m ≤ n → o ℚ.· m ≤ o ℚ.· n
≤-o· m n o x = subst2 _≤_ (·Comm m o)
                         (·Comm n o) ∘
             ≤-·o m n o x


≤-·o-cancel : ∀ m n o → 0 < o → m ℚ.· o ≤ n ℚ.· o → m ≤ n
≤-·o-cancel =
  elimProp3 {P = λ a b c → 0 < c → a ℚ.· c ≤ b ℚ.· c → a ≤ b}
            (λ x y _ → isPropΠ2 λ _ _ → isProp≤ x y)
             λ { (a , b) (c , d) (e , f) 0<e aedf≤cebf
             → inj (ℤ.0<o→≤-·o-cancel {e} {a ℤ.· ℕ₊₁→ℤ d} (subst (0 ℤ.<_) (ℤ.·IdR e) (0<e ._<_.prf))
               (subst2 ℤ._≤_ (·CommR a e (ℕ₊₁→ℤ d)) (·CommR c e (ℕ₊₁→ℤ b))
                      (ℤ.≤-·o-cancel {a ℤ.· e ℤ.· ℕ₊₁→ℤ d} {k = -1+ f}
                        (subst2 {x = a ℤ.· e ℤ.· ℕ₊₁→ℤ (d ·₊₁ f)}
                              {a ℤ.· e ℤ.· ℕ₊₁→ℤ d ℤ.· ℤ.pos (suc (-1+ f))}
                          ℤ._≤_ ℤ! ℤ! (aedf≤cebf ._≤_.prf))))) }


<-·o : ∀ m n o → 0 < o → m < n → m ℚ.· o < n ℚ.· o
<-·o =
  elimProp3 {P = λ a b c → 0 < c → a < b → a ℚ.· c < b ℚ.· c}
            (λ x y z → isPropΠ2 λ _ _ → isProp< (x ℚ.· z) (y ℚ.· z))
             λ { (a , b) (c , d) (e , f) (inj 0<e) (inj ad<cb)
             → inj (subst2 {x = a ℤ.· ℕ₊₁→ℤ d ℤ.· e ℤ.· ℕ₊₁→ℤ f}
                           {y = a ℤ.· e ℤ.· ℤ.pos (ℕ₊₁→ℕ d ℕ.· ℕ₊₁→ℕ f)}
                     ℤ._<_ (cong (ℤ._· ℕ₊₁→ℤ f) (·CommR a (ℕ₊₁→ℤ d) e) ∙
                             sym (ℤ.·Assoc (a ℤ.· e) (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ f)) ∙
                             cong (a ℤ.· e ℤ.·_) (sym (ℤ.pos·pos (ℕ₊₁→ℕ d) (ℕ₊₁→ℕ f))))
                            ℤ!
                            (ℤ.<-·o {a ℤ.· ℕ₊₁→ℤ d ℤ.· e} {k = -1+ f}
                                    (ℤ.0<o→<-·o {e} {a ℤ.· ℕ₊₁→ℤ d}
                                                (subst (0 ℤ.<_) (ℤ.·IdR e) 0<e) ad<cb))) }

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
             (λ  (a , b) (c , d) (e , f) (inj 0<e) (inj aedf<cebf)
             → inj (ℤ.0<o→<-·o-cancel {e} {a ℤ.· ℕ₊₁→ℤ d} (subst (0 ℤ.<_) (ℤ.·IdR e) 0<e)
               (subst2 ℤ._<_ (·CommR a e (ℕ₊₁→ℤ d)) (·CommR c e (ℕ₊₁→ℤ b))
                      (ℤ.<-·o-cancel {a ℤ.· e ℤ.· ℕ₊₁→ℤ d} {k = -1+ f}
                        (subst2 {x = a ℤ.· e ℤ.· ℕ₊₁→ℤ (d ·₊₁ f)}
                         {a ℤ.· e ℤ.· ℕ₊₁→ℤ d ℤ.· ℤ.pos (suc (-1+ f))}
                           ℤ._<_ ℤ! ℤ! aedf<cebf)))) )


min≤ : ∀ m n → ℚ.min m n ≤ m
min≤
    = elimProp2 {P = λ a b → ℚ.min a b ≤ a}
                (λ x y → isProp≤ (ℚ.min x y) x)
                 λ { (a , b) (c , d)
                  → inj (subst2 ℤ._≤_ (sym (ℤ.·DistPosLMin (a ℤ.· ℕ₊₁→ℤ d)
                                                       (c ℤ.· ℕ₊₁→ℤ b)
                                                       (ℕ₊₁→ℕ b)))
                                  (sym (ℤ.·Assoc a (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b)) ∙
                                   cong (a ℤ.·_) (sym (ℤ.pos·pos (ℕ₊₁→ℕ d) (ℕ₊₁→ℕ b)) ∙
                                                  cong ℕ₊₁→ℤ (·₊₁-comm d b)))
                                  (ℤ.min≤ {a ℤ.· ℕ₊₁→ℤ d ℤ.· ℕ₊₁→ℤ b}
                                           {c ℤ.· ℕ₊₁→ℤ b ℤ.· ℕ₊₁→ℤ b})) }

min≤' : ∀ m n → ℚ.min m n ≤ n
min≤' m n = subst (_≤ n) (ℚ.minComm n m) (min≤ n m)

≤→min : ∀ m n → m ≤ n → ℚ.min m n ≡ m
≤→min
    = elimProp2 {P = λ a b → a ≤ b → ℚ.min a b ≡ a}
                (λ x y → isProp→ (isSetℚ (ℚ.min x y) x))
                 λ { (a , b) (c , d) (inj ad≤cb)
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
                 (λ  (a , b) (c , d)
                  → inj (subst2 ℤ._≤_ (sym (ℤ.·Assoc a (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b)) ∙
                                   cong (a ℤ.·_) (sym (ℤ.pos·pos (ℕ₊₁→ℕ d) (ℕ₊₁→ℕ b)) ∙
                                                  cong ℕ₊₁→ℤ (·₊₁-comm d b)))
                                  (sym (ℤ.·DistPosLMax (a ℤ.· ℕ₊₁→ℤ d)
                                                       (c ℤ.· ℕ₊₁→ℤ b)
                                                       (ℕ₊₁→ℕ b)))
                                  (ℤ.≤max {a ℤ.· ℕ₊₁→ℤ d ℤ.· ℕ₊₁→ℤ b}
                                           {c ℤ.· ℕ₊₁→ℤ b ℤ.· ℕ₊₁→ℤ b})) )
≤max' : ∀ m n → n ≤ ℚ.max m n
≤max' m n = subst (n ≤_) (ℚ.maxComm n m) (≤max n m)

≤→max : ∀ m n →  m ≤ n → ℚ.max m n ≡ n
≤→max m n
    = elimProp2 {P = λ a b → a ≤ b → ℚ.max a b ≡ b}
                (λ x y → isProp→ (isSetℚ (ℚ.max x y) y))
                (λ { (a , b) (c , d) (inj ad≤cb)
                  → eq/ (ℤ.max (a ℤ.· ℕ₊₁→ℤ d)
                               (c ℤ.· ℕ₊₁→ℤ b)
                         , b ·₊₁ d)
                        (c , d)
                        (cong (ℤ._· ℕ₊₁→ℤ d) (ℤ.≤→max ad≤cb) ∙
                         sym (ℤ.·Assoc c (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ d)) ∙
                         cong (c ℤ.·_) (sym (ℤ.pos·pos (ℕ₊₁→ℕ b) (ℕ₊₁→ℕ d)))) }) m n

≤Dec : ∀ m n → Dec (m ≤ n)
≤Dec = elimProp2 (λ x y → isPropDec (isProp≤ x y))
       (λ (a , b) (c , d) → decRec (yes ∘ inj) (no ∘ _∘ _≤_.prf)
        (ℤ.≤Dec (a ℤ.· ℕ₊₁→ℤ d) (c ℤ.· ℕ₊₁→ℤ b))  )

<Dec : ∀ m n → Dec (m < n)
<Dec = elimProp2 (λ x y → isPropDec (isProp< x y))
       λ { (a , b) (c , d) → decRec (yes ∘ inj) (no ∘ _∘ _<_.prf)
        (ℤ.<Dec (a ℤ.· ℕ₊₁→ℤ d) (c ℤ.· ℕ₊₁→ℤ b)) }


_≟_ : (m n : ℚ) → Trichotomy m n
m ≟ n with discreteℚ m n
... | yes m≡n = eq m≡n
... | no m≢n with inequalityImplies# m n m≢n
...             | inl m<n = lt m<n
...             | inr n<m = gt n<m

byTrichotomy : ∀ x₀ → {A : ℚ → Type} → TrichotomyRec x₀ A → ∀ x → A x
byTrichotomy x₀ r x = TrichotomyRec.go r x (_ ≟ _)

#Dec : ∀ m n → Dec (m # n)
#Dec m n with m ≟ n
... | lt x = yes (inl x)
... | gt x = yes (inr x)
... | eq x = no (isIrrefl# n ∘ subst (_# n) x)

≡⊎# : ∀ m n → (m ≡ n) ⊎ (m # n)
≡⊎# m n with m ≟ n
... | lt x = inr (inl x)
... | gt x = inr (inr x)
... | eq x = inl x


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
                         ∣ inequalityImplies# m n m≢n ∣₁

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

≤→<minus : ∀ m n → m ≤ n → 0 ≤ n - m
≤→<minus m n x = subst (_≤ n - m) (+InvR m) (≤-+o m n (- m) x)

<minus→< : ∀ m n → 0 < n - m → m < n
<minus→< m n x = subst2 _<_ (+IdL m)
  (sym (+Assoc n (- m) m) ∙∙ cong (n ℚ.+_) (+InvL m) ∙∙ +IdR n) (<-+o 0 (n - m) m x)

≤minus→≤ : ∀ m n → 0 ≤ n - m → m ≤ n
≤minus→≤ m n x = subst2 _≤_ (+IdL m)
  (sym (+Assoc n (- m) m) ∙∙ cong (n ℚ.+_) (+InvL m) ∙∙ +IdR n) (≤-+o 0 (n - m) m x)


minus-<' : ∀ n m → - n < - m → m < n
minus-<' n m p =
  subst2 _<_ (-Invol m) (-Invol n)
   (minus-< (ℚ.- n) (ℚ.- m) p)


0<ₚ_ : ℚ → hProp ℓ-zero
0<ₚ x  = (0 < x) , isProp< _ _
-- Rec.go w
--  where
--  w : Rec (hProp ℓ-zero)
--  w .Rec.isSetB = isSetHProp
--  w .Rec.f (x , _) = (0 ℤ.< x) , ℤ.isProp<
--  w .Rec.f∼ (x , y) (x' , y') p = {!x x'!}
--   -- ⇔toPath --0<·ℕ₊₁
--   --   {!!}
--   --   {!!}
--      -- (λ u → ℤ.0<·ℕ₊₁ x' y
--      --   (subst ℤ.0<_ p (ℤ.·0< x (ℤ.pos (ℕ₊₁→ℕ y'))
--      --     u _)))
--      -- (λ u → ℤ.0<·ℕ₊₁ x y'
--      --   (subst ℤ.0<_ (sym p) (ℤ.·0< x' (ℤ.pos (ℕ₊₁→ℕ y))
--      --     u _)))

0<_ = fst ∘ 0<ₚ_

opaque
 ·0< : ∀ m n → 0< m → 0< n → 0< (m ℚ.· n)
 ·0< = elimProp2
   (λ x x' → isPropΠ2 λ _ _ → snd (0<ₚ (x ℚ.· x')) )
   λ where
     (ℤ.pos zero , snd₁) (ℤ.pos n₁ , snd₂) (inj (ℤ.pos<pos ())) _
     (ℤ.pos (suc n) , snd₁) (ℤ.pos zero , snd₂) x (inj (ℤ.pos<pos ()))
     (ℤ.pos (suc n) , snd₁) (ℤ.pos (suc n₁) , snd₂) x x₁ → inj (ℤ.pos<pos tt)

 +0< : ∀ m n → 0< m → 0< n → 0< (m ℚ.+ n)
 +0< = elimProp2
   (λ x x' → isPropΠ2 λ _ _ → snd (0<ₚ (x ℚ.+ x')) )
   λ where
     (ℤ.pos zero , snd₁) (ℤ.pos n₁ , snd₂) (inj (ℤ.pos<pos ())) _
     (ℤ.pos (suc n) , snd₁) (ℤ.pos zero , snd₂) x (inj (ℤ.pos<pos ()))
     (ℤ.pos (suc n) , snd₁) (ℤ.pos (suc n₁) , snd₂) x x₁ → inj (ℤ.pos<pos tt)

+0<' : ∀ m n o → 0< m → 0< n → (m ℚ.+ n) ≡ o → 0< o
+0<' m n o x y p = subst (0<_) p (+0< m n x y)

+₃0< : ∀ m n o → 0< m → 0< n → 0< o → 0< ((m ℚ.+ n) ℚ.+ o)
+₃0< m n o x y z = +0< (m ℚ.+ n) o (+0< m n x y) z

+₃0<' : ∀ m n o o' → 0< m → 0< n → 0< o
        → ((m ℚ.+ n) ℚ.+ o) ≡ o' → 0< o'
+₃0<' m n o o' x y z p = subst 0<_ p (+₃0< m n o x y z)


ℚ₊ : Type
ℚ₊ = Σ ℚ 0<_

infix 20 [_/_]₊

[_/_]₊ : ℕ₊₁ → ℕ₊₁ → ℚ₊
[_/_]₊ p q = [ ℕ₊₁→ℤ p , q ] , inj (ℤ.pos<pos tt)

instance
  fromNatℚ₊ : HasFromNat ℚ₊
  fromNatℚ₊ =
   record { Constraint = λ { zero → ⊥ ; _ → Unit }
             ; fromNat = λ { (suc n) → ([ ℤ.pos (suc n) , 1 ] , inj (ℤ.pos<pos tt)) } }

ℚ₊≡ : {x y : ℚ₊} → fst x ≡ fst y → x ≡ y
ℚ₊≡ = Σ≡Prop (snd ∘ 0<ₚ_)

_ℚ₊·_ : ℚ₊ → ℚ₊ → ℚ₊
_ℚ₊·_ x x₁ = ((fst x) ℚ.· (fst x₁)) ,
  ·0< (fst x) (fst x₁) (snd x) (snd x₁)

_ℚ₊+_ : ℚ₊ → ℚ₊ → ℚ₊
_ℚ₊+_ x x₁ = ((fst x) ℚ.+ (fst x₁)) ,
  +0< (fst x) (fst x₁) (snd x) (snd x₁)

0<→< : ∀ q → 0< q → 0 < q
0<→< q x = x

0<ℚ₊ : (ε : ℚ₊) → 0 < fst ε
0<ℚ₊ = uncurry 0<→<

0≤ℚ₊ : (ε : ℚ₊) → 0 ≤ fst ε
0≤ℚ₊ ε = <Weaken≤ 0 (fst ε) (uncurry 0<→< ε)


<→0< : ∀ q → 0 < q → 0< q
<→0< q x = x

0<-min : ∀ x y → 0< x → 0< y → 0< (ℚ.min x y)
0<-min = elimProp2
 (λ x y → isPropΠ2 λ _ _ → snd (0<ₚ (ℚ.min x y)))
  λ where
    (ℤ.pos zero , snd₁) (ℤ.pos n₁ , snd₂) (inj (ℤ.pos<pos ())) _
    (ℤ.pos (suc n) , snd₁) (ℤ.pos zero , snd₂) x (inj (ℤ.pos<pos ()))
    (ℤ.pos (suc n) , snd₁) (ℤ.pos (suc n₁) , snd₂) x x₁ →
      subst (0 <_) (cong (λ m → [ ℤ.pos m , _ ]) (sym minSuc)) (inj (ℤ.pos<pos _))

min₊ : ℚ₊ → ℚ₊ → ℚ₊
min₊ (x , y) (x' , y') =
  ℚ.min x x' , 0<-min x x' y y'

max₊ : ℚ₊ → ℚ₊ → ℚ₊
max₊ (x , y) (x' , y') =
  ℚ.max x x' , <→0< (ℚ.max x x') (isTrans<≤ 0 x _ (0<→< x y) (≤max x x'))

-- min< : ∀ n m → n < m →  ℚ.min n m ≡ n
-- min< = elimProp2 (λ _ _ → isPropΠ λ _ → isSetℚ _ _)
--   λ (x , 1+ y) (x' , 1+ y') (inj (u , p)) →
--     eq/ _ _
--      (ℤ.·DistPosLMin _ _ _ ∙ {!!})
-- -- with n ≟ m
-- -- ... | lt x₁ = {!x!}
-- -- ... | eq x₁ = cong (ℚ.min n) (sym x₁) ∙ minIdem n
-- -- ... | gt x₁ = {!x!}

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

≤≃≡⊎< : ∀ q r → (q ≤ r) ≃ ((q ≡ r) ⊎ (q < r))
≤≃≡⊎< q r = propBiimpl→Equiv
  (isProp≤ q r)
  (⊎.isProp⊎ (isSetℚ _ _) ((isProp< q r)) λ u v → ≤→≯ r q (≡Weaken≤ _ _ (sym u)) v)
    (≤→≡⊎< q r) (⊎.rec (≡Weaken≤ _ _) (<Weaken≤ q r))

≤ℤ→≤ℚ : ∀ m n → m ℤ.≤ n → [ m , 1 ] ≤ [ n , 1 ]
≤ℤ→≤ℚ m n = inj ∘S (subst2 ℤ._≤_ (sym (ℤ.·IdR m)) (sym (ℤ.·IdR n)))

<ℤ→<ℚ : ∀ m n → m ℤ.< n → [ m , 1 ] < [ n , 1 ]
<ℤ→<ℚ m n = inj ∘S subst2 ℤ._<_ (sym (ℤ.·IdR m)) (sym (ℤ.·IdR n))

[k/n]<[k'/n] : ∀ k k' n → k ℤ.< k' → ([ ( k , n ) ]) < ([ (k' , n) ])
[k/n]<[k'/n] k k' n k<k' = inj (ℤ.<-·o {k} k<k')

[k/n]≤[k'/n] : ∀ k k' n → k ℤ.≤ k' → ([ ( k , n ) ]) ≤ ([ (k' , n) ])
[k/n]≤[k'/n] k k' n k<k' = inj (ℤ.≤-·o {k} k<k')


eqElim₊ : (lrhs : ℚ₊ → ℚ × ℚ) →
  (∀ {k m} → fst (lrhs ([ ((ℤ.pos (suc k)) , 1+ m) ] , inj (ℤ.pos<pos tt)))
        ≡  snd (lrhs ([ ((ℤ.pos (suc k)) , 1+ m) ] , inj (ℤ.pos<pos tt))))
    → ∀ (ε : ℚ₊) → fst (lrhs ε) ≡ snd (lrhs ε)
eqElim₊ lrhs p = uncurry (ElimProp.go w)
  where
  w : ElimProp (λ z → ∀ p →  fst (lrhs (z , p)) ≡ snd (lrhs (z , p)))
  w .ElimProp.isPropB _ = isPropΠ λ _ → isSetℚ _ _
  w .ElimProp.f (ℤ.pos (suc n) , (1+ n₁)) (inj (ℤ.pos<pos _)) = p {n} {n₁}


substℚ₊ : ∀ {ℓ} (A : ℚ → Type ℓ) (lrhs : ℚ₊ → ℚ × ℚ) →
  (∀ {k m} → fst (lrhs ([ ((ℤ.pos (suc k)) , 1+ m) ] , inj (ℤ.pos<pos tt)))
        ≡  snd (lrhs ([ ((ℤ.pos (suc k)) , 1+ m) ] , inj (ℤ.pos<pos tt))))
    → ∀ (ε : ℚ₊) → A (fst (lrhs ε)) → A (snd (lrhs ε))
substℚ₊ A lrhs p ε =
  subst A (eqElim₊ lrhs p ε)


eqElim₂₊ : {lhs rhs : ℚ₊ → ℚ₊ → ℚ} →
  (∀ k m k' m' → lhs ([ ((ℤ.pos (suc k)) , 1+ m) ] , inj (ℤ.pos<pos tt))
          ([ ((ℤ.pos (suc k')) , 1+ m') ] , inj (ℤ.pos<pos tt))
        ≡  rhs ([ ((ℤ.pos (suc k)) , 1+ m) ] , inj (ℤ.pos<pos tt))
         ([ ((ℤ.pos (suc k')) , 1+ m') ] , inj (ℤ.pos<pos tt)))
    → ∀ {ε ε' : ℚ₊} → lhs ε ε' ≡ rhs ε ε'
eqElim₂₊ {lhs} {rhs} p {ε , 0<ε} {ε' , 0<ε'} = ElimProp2.go w ε ε' 0<ε 0<ε'
  where
  w : ElimProp2 (λ z z' → ∀ p p' →  lhs (z , p) (z' , p') ≡ rhs (z , p) (z' , p'))
  w .ElimProp2.isPropB _ _ = isPropΠ2 λ _ _ → isSetℚ _ _
  w .ElimProp2.f (ℤ.pos (suc n) , (1+ n₁)) (ℤ.pos (suc m) , (1+ m₁)) (inj (ℤ.pos<pos _)) (inj (ℤ.pos<pos _)) =
    p n n₁ m m₁


module EqElims where
 data ℚTypes : Type where
  [ℚ] [ℚ₊] : ℚTypes

 ℚSignature : Type
 ℚSignature = List ℚTypes

 lrhsDom : ℚTypes → Type
 lrhsDom [ℚ] = ℚ
 lrhsDom [ℚ₊] = ℚ₊


 lrhsDomFst : ℚTypes → Type
 lrhsDomFst [ℚ] = ℤ
 lrhsDomFst [ℚ₊] = ℕ₊₁

 lrhsCtr : ∀ b → lrhsDomFst b → ℕ₊₁ → (lrhsDom b)
 lrhsCtr [ℚ] k m = [ k , m ]
 lrhsCtr [ℚ₊] n m = [ ℕ₊₁→ℤ n , m ] , inj (ℤ.pos<pos tt)

 LRhs : ℚSignature → Type
 LRhs [] = ℚ × ℚ
 LRhs (x ∷ xs) = lrhsDom x → LRhs xs

 LemType : ∀ s → LRhs s → Type
 LemType [] (lhs , rhs) = lhs ≡ rhs
 LemType (x ∷ xs) lrhs = (k : lrhsDomFst x) (m : ℕ₊₁) → LemType xs (lrhs (lrhsCtr x k m))


 EqType : ∀ s → LRhs s → Type
 EqType [] (lhs , rhs) = lhs ≡ rhs
 EqType (x ∷ xs) lrhs = (q : lrhsDom x) → EqType xs (lrhs q)

 isPropEqType : ∀ s → (lrhs : LRhs s) → isProp (EqType s lrhs)
 isPropEqType [] lrhs = isSetℚ _ _
 isPropEqType (_ ∷ s) lrhs = isPropΠ $ isPropEqType s ∘ lrhs

 EllimEqₛ : ∀ s → (lrhs : LRhs s) → LemType s lrhs → EqType s lrhs
 EllimEqₛ [] lrhs e = e
 EllimEqₛ ([ℚ] ∷ xs) lrhs e = ElimProp.go w
  where
  w : ElimProp _
  w .ElimProp.isPropB = isPropEqType xs ∘ lrhs
  w .ElimProp.f (k , m) = EllimEqₛ xs (lrhs _) (e k m)

 EllimEqₛ ([ℚ₊] ∷ xs) lrhs e = uncurry (ElimProp.go w)
  where
  w : ElimProp (λ z → ∀ p → EqType xs (lrhs (z , p)))
  w .ElimProp.isPropB q = isPropΠ λ _ → isPropEqType xs (lrhs (q , _))
  w .ElimProp.f (ℤ.pos (suc n) , m) (inj (ℤ.pos<pos _)) = EllimEqₛ xs (lrhs _) (e (1+ n) m)



ℚintervalℙ : ℚ → ℚ → ℙ ℚ
ℚintervalℙ a b x = ((a ≤ x) × (x ≤ b)) ,
  isProp× (isProp≤ _ _)  (isProp≤ _ _)

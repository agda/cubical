{-# OPTIONS --safe #-}
module Cubical.Data.Rationals.MoreRationals.QuoQ.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws hiding (_⁻¹)
open import Cubical.Foundations.Univalence

open import Cubical.Data.Int.MoreInts.QuoInt as ℤ using (ℤ; Sign; signed; pos; neg; posneg; sign)
open import Cubical.HITs.SetQuotients as SetQuotient using () renaming (_/_ to _//_)

open import Cubical.Data.Nat as ℕ using (ℕ; zero; suc)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Sigma

open import Cubical.Data.Sum
open import Cubical.Relation.Nullary

open import Cubical.Data.Rationals.MoreRationals.QuoQ.Base

ℚ-cancelˡ : ∀ {a b} (c : ℕ₊₁) → [ ℕ₊₁→ℤ c ℤ.· a / c ·₊₁ b ] ≡ [ a / b ]
ℚ-cancelˡ {a} {b} c = eq/ _ _
  (cong (ℤ._· ℕ₊₁→ℤ b) (ℤ.·-comm (ℕ₊₁→ℤ c) a) ∙ sym (ℤ.·-assoc a (ℕ₊₁→ℤ c) (ℕ₊₁→ℤ b)))

ℚ-cancelʳ : ∀ {a b} (c : ℕ₊₁) → [ a ℤ.· ℕ₊₁→ℤ c / b ·₊₁ c ] ≡ [ a / b ]
ℚ-cancelʳ {a} {b} c = eq/ _ _
  (sym (ℤ.·-assoc a (ℕ₊₁→ℤ c) (ℕ₊₁→ℤ b)) ∙ cong (a ℤ.·_) (ℤ.·-comm (ℕ₊₁→ℤ c) (ℕ₊₁→ℤ b)))

-- useful functions for defining operations on ℚ

onCommonDenom :
  (g : ℤ × ℕ₊₁ → ℤ × ℕ₊₁ → ℤ)
  (g-eql : ∀ ((a , b) (c , d) (e , f) : ℤ × ℕ₊₁) (p : a ℤ.· ℕ₊₁→ℤ d ≡ c ℤ.· ℕ₊₁→ℤ b)
           → ℕ₊₁→ℤ d ℤ.· (g (a , b) (e , f)) ≡ ℕ₊₁→ℤ b ℤ.· (g (c , d) (e , f)))
  (g-eqr : ∀ ((a , b) (c , d) (e , f) : ℤ × ℕ₊₁) (p : c ℤ.· ℕ₊₁→ℤ f ≡ e ℤ.· ℕ₊₁→ℤ d)
           → (g (a , b) (c , d)) ℤ.· ℕ₊₁→ℤ f ≡ (g (a , b) (e , f)) ℤ.· ℕ₊₁→ℤ d)
  → ℚ → ℚ → ℚ
onCommonDenom g g-eql g-eqr = SetQuotient.rec2 isSetℚ
  (λ { (a , b) (c , d) → [ g (a , b) (c , d) / b ·₊₁ d ] })
  (λ { (a , b) (c , d) (e , f) p → eql (a , b) (c , d) (e , f) p })
  (λ { (a , b) (c , d) (e , f) p → eqr (a , b) (c , d) (e , f) p })
  where eql : ∀ ((a , b) (c , d) (e , f) : ℤ × ℕ₊₁) (p : a ℤ.· ℕ₊₁→ℤ d ≡ c ℤ.· ℕ₊₁→ℤ b)
              → [ g (a , b) (e , f) / b ·₊₁ f ] ≡ [ g (c , d) (e , f) / d ·₊₁ f ]
        eql (a , b) (c , d) (e , f) p =
          [ g (a , b) (e , f) / b ·₊₁ f ]
            ≡⟨ sym (ℚ-cancelˡ d) ⟩
          [ ℕ₊₁→ℤ d ℤ.· (g (a , b) (e , f)) / d ·₊₁ (b ·₊₁ f) ]
            ≡[ i ]⟨ [ ℕ₊₁→ℤ d ℤ.· (g (a , b) (e , f)) / ·₊₁-assoc d b f i ] ⟩
          [ ℕ₊₁→ℤ d ℤ.· (g (a , b) (e , f)) / (d ·₊₁ b) ·₊₁ f ]
            ≡[ i ]⟨ [ g-eql (a , b) (c , d) (e , f) p i / ·₊₁-comm d b i ·₊₁ f ] ⟩
          [ ℕ₊₁→ℤ b ℤ.· (g (c , d) (e , f)) / (b ·₊₁ d) ·₊₁ f ]
            ≡[ i ]⟨ [ ℕ₊₁→ℤ b ℤ.· (g (c , d) (e , f)) / ·₊₁-assoc b d f (~ i) ] ⟩
          [ ℕ₊₁→ℤ b ℤ.· (g (c , d) (e , f)) / b ·₊₁ (d ·₊₁ f) ]
            ≡⟨ ℚ-cancelˡ b ⟩
          [ g (c , d) (e , f) / d ·₊₁ f ] ∎
        eqr : ∀ ((a , b) (c , d) (e , f) : ℤ × ℕ₊₁) (p : c ℤ.· ℕ₊₁→ℤ f ≡ e ℤ.· ℕ₊₁→ℤ d)
             → [ g (a , b) (c , d) / b ·₊₁ d ] ≡ [ g (a , b) (e , f) / b ·₊₁ f ]
        eqr (a , b) (c , d) (e , f) p =
          [ g (a , b) (c , d) / b ·₊₁ d ]
            ≡⟨ sym (ℚ-cancelʳ f) ⟩
          [ (g (a , b) (c , d)) ℤ.· ℕ₊₁→ℤ f / (b ·₊₁ d) ·₊₁ f ]
            ≡[ i ]⟨ [ (g (a , b) (c , d)) ℤ.· ℕ₊₁→ℤ f / ·₊₁-assoc b d f (~ i) ] ⟩
          [ (g (a , b) (c , d)) ℤ.· ℕ₊₁→ℤ f / b ·₊₁ (d ·₊₁ f) ]
            ≡[ i ]⟨ [ g-eqr (a , b) (c , d) (e , f) p i / b ·₊₁ ·₊₁-comm d f i ] ⟩
          [ (g (a , b) (e , f)) ℤ.· ℕ₊₁→ℤ d / b ·₊₁ (f ·₊₁ d) ]
            ≡[ i ]⟨ [ (g (a , b) (e , f)) ℤ.· ℕ₊₁→ℤ d / ·₊₁-assoc b f d i ] ⟩
          [ (g (a , b) (e , f)) ℤ.· ℕ₊₁→ℤ d / (b ·₊₁ f) ·₊₁ d ]
            ≡⟨ ℚ-cancelʳ d ⟩
          [ g (a , b) (e , f) / b ·₊₁ f ] ∎

onCommonDenomSym :
  (g : ℤ × ℕ₊₁ → ℤ × ℕ₊₁ → ℤ)
  (g-sym : ∀ x y → g x y ≡ g y x)
  (g-eql : ∀ ((a , b) (c , d) (e , f) : ℤ × ℕ₊₁) (p : a ℤ.· ℕ₊₁→ℤ d ≡ c ℤ.· ℕ₊₁→ℤ b)
           → ℕ₊₁→ℤ d ℤ.· (g (a , b) (e , f)) ≡ ℕ₊₁→ℤ b ℤ.· (g (c , d) (e , f)))
  → ℚ → ℚ → ℚ
onCommonDenomSym g g-sym g-eql = onCommonDenom g g-eql q-eqr
  where q-eqr : ∀ ((a , b) (c , d) (e , f) : ℤ × ℕ₊₁) (p : c ℤ.· ℕ₊₁→ℤ f ≡ e ℤ.· ℕ₊₁→ℤ d)
                → (g (a , b) (c , d)) ℤ.· ℕ₊₁→ℤ f ≡ (g (a , b) (e , f)) ℤ.· ℕ₊₁→ℤ d
        q-eqr (a , b) (c , d) (e , f) p =
          (g (a , b) (c , d)) ℤ.· ℕ₊₁→ℤ f ≡[ i ]⟨ ℤ.·-comm (g-sym (a , b) (c , d) i) (ℕ₊₁→ℤ f) i ⟩
          ℕ₊₁→ℤ f ℤ.· (g (c , d) (a , b)) ≡⟨ g-eql (c , d) (e , f) (a , b) p ⟩
          ℕ₊₁→ℤ d ℤ.· (g (e , f) (a , b)) ≡[ i ]⟨ ℤ.·-comm (ℕ₊₁→ℤ d) (g-sym (e , f) (a , b) i) i ⟩
          (g (a , b) (e , f)) ℤ.· ℕ₊₁→ℤ d ∎

onCommonDenomSym-comm : ∀ {g} g-sym {g-eql} (x y : ℚ)
                        → onCommonDenomSym g g-sym g-eql x y ≡
                          onCommonDenomSym g g-sym g-eql y x
onCommonDenomSym-comm g-sym = SetQuotient.elimProp2 (λ _ _ → isSetℚ _ _)
  (λ { (a , b) (c , d) i → [ g-sym (a , b) (c , d) i / ·₊₁-comm b d i ] })


-- basic arithmetic operations on ℚ

infixl 6 _+_
infixl 7 _·_

private
  lem₁ : ∀ a b c d e (p : a ℤ.· b ≡ c ℤ.· d) → b ℤ.· (a ℤ.· e) ≡ d ℤ.· (c ℤ.· e)
  lem₁ a b c d e p =   ℤ.·-assoc b a e
                     ∙ cong (ℤ._· e) (ℤ.·-comm b a ∙ p ∙ ℤ.·-comm c d)
                     ∙ sym (ℤ.·-assoc d c e)

  lem₂ : ∀ a b c → a ℤ.· (b ℤ.· c) ≡ c ℤ.· (b ℤ.· a)
  lem₂ a b c =   cong (a ℤ.·_) (ℤ.·-comm b c) ∙ ℤ.·-assoc a c b
               ∙ cong (ℤ._· b) (ℤ.·-comm a c) ∙ sym (ℤ.·-assoc c a b)
               ∙ cong (c ℤ.·_) (ℤ.·-comm a b)

_+_ : ℚ → ℚ → ℚ
_+_ = onCommonDenomSym
  (λ { (a , b) (c , d) → a ℤ.· (ℕ₊₁→ℤ d) ℤ.+ c ℤ.· (ℕ₊₁→ℤ b) })
  (λ { (a , b) (c , d) → ℤ.+-comm (a ℤ.· (ℕ₊₁→ℤ d)) (c ℤ.· (ℕ₊₁→ℤ b)) })
  (λ { (a , b) (c , d) (e , f) p →
    ℕ₊₁→ℤ d ℤ.· (a ℤ.· ℕ₊₁→ℤ f ℤ.+ e ℤ.· ℕ₊₁→ℤ b)
      ≡⟨ sym (ℤ.·-distribˡ (ℕ₊₁→ℤ d) (a ℤ.· ℕ₊₁→ℤ f) (e ℤ.· ℕ₊₁→ℤ b)) ⟩
    ℕ₊₁→ℤ d ℤ.· (a ℤ.· ℕ₊₁→ℤ f) ℤ.+ ℕ₊₁→ℤ d ℤ.· (e ℤ.· ℕ₊₁→ℤ b)
      ≡[ i ]⟨ lem₁ a (ℕ₊₁→ℤ d) c (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ f) p i ℤ.+ lem₂ (ℕ₊₁→ℤ d) e (ℕ₊₁→ℤ b) i ⟩
    ℕ₊₁→ℤ b ℤ.· (c ℤ.· ℕ₊₁→ℤ f) ℤ.+ ℕ₊₁→ℤ b ℤ.· (e ℤ.· ℕ₊₁→ℤ d)
      ≡⟨ ℤ.·-distribˡ (ℕ₊₁→ℤ b) (c ℤ.· ℕ₊₁→ℤ f) (e ℤ.· ℕ₊₁→ℤ d) ⟩
    ℕ₊₁→ℤ b ℤ.· (c ℤ.· ℕ₊₁→ℤ f ℤ.+ e ℤ.· ℕ₊₁→ℤ d) ∎ })

+-comm : ∀ x y → x + y ≡ y + x
+-comm = onCommonDenomSym-comm
  (λ { (a , b) (c , d) → ℤ.+-comm (a ℤ.· (ℕ₊₁→ℤ d)) (c ℤ.· (ℕ₊₁→ℤ b)) })

+-identityˡ : ∀ x → 0 + x ≡ x
+-identityˡ = SetQuotient.elimProp (λ _ → isSetℚ _ _)
  (λ { (a , b) i → [ ℤ.·-identityʳ a i / ·₊₁-identityˡ b i ] })

+-identityʳ : ∀ x → x + 0 ≡ x
+-identityʳ x = +-comm x _ ∙ +-identityˡ x

+-assoc : ∀ x y z → x + (y + z) ≡ (x + y) + z
+-assoc = SetQuotient.elimProp3 (λ _ _ _ → isSetℚ _ _)
  (λ { (a , b) (c , d) (e , f) i → [ eq a (ℕ₊₁→ℤ b) c (ℕ₊₁→ℤ d) e (ℕ₊₁→ℤ f) i / ·₊₁-assoc b d f i ] })
  where eq₁ : ∀ a b c → (a ℤ.· b) ℤ.· c ≡ a ℤ.· (c ℤ.· b)
        eq₁ a b c = sym (ℤ.·-assoc a b c) ∙ cong (a ℤ.·_) (ℤ.·-comm b c)
        eq₂ : ∀ a b c → (a ℤ.· b) ℤ.· c ≡ (a ℤ.· c) ℤ.· b
        eq₂ a b c = eq₁ a b c ∙ ℤ.·-assoc a c b

        eq : ∀ a b c d e f → Path ℤ _ _
        eq a b c d e f =
          a ℤ.· (d ℤ.· f) ℤ.+ (c ℤ.· f ℤ.+ e ℤ.· d) ℤ.· b
            ≡[ i ]⟨ a ℤ.· (d ℤ.· f) ℤ.+ ℤ.·-distribʳ (c ℤ.· f) (e ℤ.· d) b (~ i) ⟩
          a ℤ.· (d ℤ.· f) ℤ.+ ((c ℤ.· f) ℤ.· b ℤ.+ (e ℤ.· d) ℤ.· b)
            ≡[ i ]⟨ ℤ.+-assoc (ℤ.·-assoc a d f i) (eq₂ c f b i) (eq₁ e d b i) i ⟩
          ((a ℤ.· d) ℤ.· f ℤ.+ (c ℤ.· b) ℤ.· f) ℤ.+ e ℤ.· (b ℤ.· d)
            ≡[ i ]⟨ ℤ.·-distribʳ (a ℤ.· d) (c ℤ.· b) f i ℤ.+ e ℤ.· (b ℤ.· d) ⟩
          (a ℤ.· d ℤ.+ c ℤ.· b) ℤ.· f ℤ.+ e ℤ.· (b ℤ.· d) ∎


_·_ : ℚ → ℚ → ℚ
_·_ = onCommonDenomSym
  (λ { (a , _) (c , _) → a ℤ.· c })
  (λ { (a , _) (c , _) → ℤ.·-comm a c })
  (λ { (a , b) (c , d) (e , _) p → lem₁ a (ℕ₊₁→ℤ d) c (ℕ₊₁→ℤ b) e p })

·-comm : ∀ x y → x · y ≡ y · x
·-comm = onCommonDenomSym-comm (λ { (a , _) (c , _) → ℤ.·-comm a c })

·-identityˡ : ∀ x → 1 · x ≡ x
·-identityˡ = SetQuotient.elimProp (λ _ → isSetℚ _ _)
  (λ { (a , b) i → [ ℤ.·-identityˡ a i / ·₊₁-identityˡ b i ] })

·-identityʳ : ∀ x → x · 1 ≡ x
·-identityʳ = SetQuotient.elimProp (λ _ → isSetℚ _ _)
  (λ { (a , b) i → [ ℤ.·-identityʳ a i / ·₊₁-identityʳ b i ] })

·-zeroˡ : ∀ x → 0 · x ≡ 0
·-zeroˡ = SetQuotient.elimProp (λ _ → isSetℚ _ _)
  (λ { (a , b) → (λ i → [ p a b i / 1 ·₊₁ b ]) ∙ ℚ-cancelʳ b })
  where p : ∀ a b → 0 ℤ.· a ≡ 0 ℤ.· ℕ₊₁→ℤ b
        p a b = ℤ.·-zeroˡ {ℤ.spos} a ∙ sym (ℤ.·-zeroˡ {ℤ.spos} (ℕ₊₁→ℤ b))

·-zeroʳ : ∀ x → x · 0 ≡ 0
·-zeroʳ = SetQuotient.elimProp (λ _ → isSetℚ _ _)
  (λ { (a , b) → (λ i → [ p a b i / b ·₊₁ 1 ]) ∙ ℚ-cancelˡ b })
  where p : ∀ a b → a ℤ.· 0 ≡ ℕ₊₁→ℤ b ℤ.· 0
        p a b = ℤ.·-zeroʳ {ℤ.spos} a ∙ sym (ℤ.·-zeroʳ {ℤ.spos} (ℕ₊₁→ℤ b))

·-assoc : ∀ x y z → x · (y · z) ≡ (x · y) · z
·-assoc = SetQuotient.elimProp3 (λ _ _ _ → isSetℚ _ _)
  (λ { (a , b) (c , d) (e , f) i → [ ℤ.·-assoc a c e i / ·₊₁-assoc b d f i ] })

·-distribˡ : ∀ x y z → (x · y) + (x · z) ≡ x · (y + z)
·-distribˡ = SetQuotient.elimProp3 (λ _ _ _ → isSetℚ _ _)
  (λ { (a , b) (c , d) (e , f) → eq a b c d e f })
  where lem : ∀ {ℓ} {A : Type ℓ} (_·_ : A → A → A)
                (·-comm : ∀ x y → x · y ≡ y · x)
                (·-assoc : ∀ x y z → x · (y · z) ≡ (x · y) · z)
                a c b d
              → (a · c) · (b · d) ≡ (a · (c · d)) · b
        lem _·_ ·-comm ·-assoc a c b d =
          (a · c) · (b · d) ≡[ i ]⟨ (a · c) · ·-comm b d i ⟩
          (a · c) · (d · b) ≡⟨ ·-assoc (a · c) d b ⟩
          ((a · c) · d) · b ≡[ i ]⟨ ·-assoc a c d (~ i) · b ⟩
          (a · (c · d)) · b ∎

        lemℤ   = lem ℤ._·_ ℤ.·-comm ℤ.·-assoc
        lemℕ₊₁ = lem _·₊₁_ ·₊₁-comm ·₊₁-assoc

        eq : ∀ a b c d e f →
               [ (a ℤ.· c) ℤ.· ℕ₊₁→ℤ (b ·₊₁ f) ℤ.+ (a ℤ.· e) ℤ.· ℕ₊₁→ℤ (b ·₊₁ d)
                 / (b ·₊₁ d) ·₊₁ (b ·₊₁ f) ]
             ≡ [ a ℤ.· (c ℤ.· ℕ₊₁→ℤ f ℤ.+ e ℤ.· ℕ₊₁→ℤ d)
                / b ·₊₁ (d ·₊₁ f) ]
        eq a b c d e f =
          (λ i → [ lemℤ a c (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ f) i ℤ.+ lemℤ a e (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ d) i
                   / lemℕ₊₁ b d b f i ]) ∙
          (λ i → [ ℤ.·-distribʳ (a ℤ.· (c ℤ.· ℕ₊₁→ℤ f)) (a ℤ.· (e ℤ.· ℕ₊₁→ℤ d)) (ℕ₊₁→ℤ b) i
                   / (b ·₊₁ (d ·₊₁ f)) ·₊₁ b ]) ∙
          ℚ-cancelʳ {a ℤ.· (c ℤ.· ℕ₊₁→ℤ f) ℤ.+ a ℤ.· (e ℤ.· ℕ₊₁→ℤ d)} {b ·₊₁ (d ·₊₁ f)} b ∙
          (λ i → [ ℤ.·-distribˡ a (c ℤ.· ℕ₊₁→ℤ f) (e ℤ.· ℕ₊₁→ℤ d) i
                   / b ·₊₁ (d ·₊₁ f) ])

·-distribʳ : ∀ x y z → (x · z) + (y · z) ≡ (x + y) · z
·-distribʳ x y z = (λ i → ·-comm x z i + ·-comm y z i) ∙ ·-distribˡ z x y ∙ ·-comm z (x + y)


-_ : ℚ → ℚ
- x = -1 · x

negate-invol : ∀ x → - - x ≡ x
negate-invol x = ·-assoc -1 -1 x ∙ ·-identityˡ x

negateEquiv : ℚ ≃ ℚ
negateEquiv = isoToEquiv (iso -_ -_ negate-invol negate-invol)

negateEq : ℚ ≡ ℚ
negateEq = ua negateEquiv

+-inverseˡ : ∀ x → (- x) + x ≡ 0
+-inverseˡ x = (λ i → (-1 · x) + ·-identityˡ x (~ i)) ∙ ·-distribʳ -1 1 x ∙ ·-zeroˡ x

_-_ : ℚ → ℚ → ℚ
x - y = x + (- y)

+-inverseʳ : ∀ x → x - x ≡ 0
+-inverseʳ x = +-comm x (- x) ∙ +-inverseˡ x

+-injˡ : ∀ x y z → x + y ≡ x + z → y ≡ z
+-injˡ x y z p = sym (q y) ∙ cong ((- x) +_) p ∙ q z
  where q : ∀ y → (- x) + (x + y) ≡ y
        q y = +-assoc (- x) x y ∙ cong (_+ y) (+-inverseˡ x) ∙ +-identityˡ y

+-injʳ : ∀ x y z → x + y ≡ z + y → x ≡ z
+-injʳ x y z p = +-injˡ y x z (+-comm y x ∙ p ∙ +-comm z y)

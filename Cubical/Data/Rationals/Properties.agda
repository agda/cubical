{-# OPTIONS --safe #-}
module Cubical.Data.Rationals.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws hiding (_⁻¹)
open import Cubical.Foundations.Univalence

open import Cubical.Data.Int as ℤ using (ℤ; pos·pos; pos0+)
open import Cubical.HITs.SetQuotients as SetQuotient using () renaming (_/_ to _//_)

open import Cubical.Data.Nat as ℕ using (ℕ; zero; suc)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Sigma

open import Cubical.Data.Sum
open import Cubical.Relation.Nullary

open import Cubical.Data.Rationals.Base

·CancelL : ∀ {a b} (c : ℕ₊₁) → [ ℕ₊₁→ℤ c ℤ.· a / c ·₊₁ b ] ≡ [ a / b ]
·CancelL {a} {b} c = eq/ _ _
  ((ℕ₊₁→ℤ c ℤ.· a)   ℤ.· ℕ₊₁→ℤ b  ≡⟨ cong (ℤ._· ℕ₊₁→ℤ b) (ℤ.·Comm (ℕ₊₁→ℤ c) a) ⟩
   (a ℤ.· (ℕ₊₁→ℤ c)) ℤ.· ℕ₊₁→ℤ b  ≡⟨ sym (ℤ.·Assoc a (ℕ₊₁→ℤ c) (ℕ₊₁→ℤ b)) ⟩
    a ℤ.· (ℕ₊₁→ℤ c   ℤ.· ℕ₊₁→ℤ b) ≡⟨ cong (a ℤ.·_) (sym (pos·pos (ℕ₊₁→ℕ c) (ℕ₊₁→ℕ b))) ⟩
    a ℤ.·  ℕ₊₁→ℤ (c ·₊₁ b)         ∎)

·CancelR : ∀ {a b} (c : ℕ₊₁) → [ a ℤ.· ℕ₊₁→ℤ c / b ·₊₁ c ] ≡ [ a / b ]
·CancelR {a} {b} c = eq/ _ _
  (a ℤ.·  ℕ₊₁→ℤ c ℤ.· ℕ₊₁→ℤ b   ≡⟨ sym (ℤ.·Assoc a (ℕ₊₁→ℤ c) (ℕ₊₁→ℤ b)) ⟩
   a ℤ.· (ℕ₊₁→ℤ c ℤ.· ℕ₊₁→ℤ b)  ≡⟨ cong (a ℤ.·_) (ℤ.·Comm (ℕ₊₁→ℤ c) (ℕ₊₁→ℤ b)) ⟩
   a ℤ.· (ℕ₊₁→ℤ b ℤ.· ℕ₊₁→ℤ c)  ≡⟨ cong (a ℤ.·_) (sym (pos·pos (ℕ₊₁→ℕ b) (ℕ₊₁→ℕ c))) ⟩
   a ℤ.· ℕ₊₁→ℤ (b ·₊₁ c) ∎)

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
  where abstract
        eql : ∀ ((a , b) (c , d) (e , f) : ℤ × ℕ₊₁) (p : a ℤ.· ℕ₊₁→ℤ d ≡ c ℤ.· ℕ₊₁→ℤ b)
              → [ g (a , b) (e , f) / b ·₊₁ f ] ≡ [ g (c , d) (e , f) / d ·₊₁ f ]
        eql (a , b) (c , d) (e , f) p =
          [ g (a , b) (e , f) / b ·₊₁ f ]
            ≡⟨ sym (·CancelL d) ⟩
          [ ℕ₊₁→ℤ d ℤ.· (g (a , b) (e , f)) / d ·₊₁ (b ·₊₁ f) ]
            ≡[ i ]⟨ [ ℕ₊₁→ℤ d ℤ.· (g (a , b) (e , f)) / ·₊₁-assoc d b f i ] ⟩
          [ ℕ₊₁→ℤ d ℤ.· (g (a , b) (e , f)) / (d ·₊₁ b) ·₊₁ f ]
            ≡[ i ]⟨ [ g-eql (a , b) (c , d) (e , f) p i / ·₊₁-comm d b i ·₊₁ f ] ⟩
          [ ℕ₊₁→ℤ b ℤ.· (g (c , d) (e , f)) / (b ·₊₁ d) ·₊₁ f ]
            ≡[ i ]⟨ [ ℕ₊₁→ℤ b ℤ.· (g (c , d) (e , f)) / ·₊₁-assoc b d f (~ i) ] ⟩
          [ ℕ₊₁→ℤ b ℤ.· (g (c , d) (e , f)) / b ·₊₁ (d ·₊₁ f) ]
            ≡⟨ ·CancelL b ⟩
          [ g (c , d) (e , f) / d ·₊₁ f ] ∎
        eqr : ∀ ((a , b) (c , d) (e , f) : ℤ × ℕ₊₁) (p : c ℤ.· ℕ₊₁→ℤ f ≡ e ℤ.· ℕ₊₁→ℤ d)
             → [ g (a , b) (c , d) / b ·₊₁ d ] ≡ [ g (a , b) (e , f) / b ·₊₁ f ]
        eqr (a , b) (c , d) (e , f) p =
          [ g (a , b) (c , d) / b ·₊₁ d ]
            ≡⟨ sym (·CancelR f) ⟩
          [ (g (a , b) (c , d)) ℤ.· ℕ₊₁→ℤ f / (b ·₊₁ d) ·₊₁ f ]
            ≡[ i ]⟨ [ (g (a , b) (c , d)) ℤ.· ℕ₊₁→ℤ f / ·₊₁-assoc b d f (~ i) ] ⟩
          [ (g (a , b) (c , d)) ℤ.· ℕ₊₁→ℤ f / b ·₊₁ (d ·₊₁ f) ]
            ≡[ i ]⟨ [ g-eqr (a , b) (c , d) (e , f) p i / b ·₊₁ ·₊₁-comm d f i ] ⟩
          [ (g (a , b) (e , f)) ℤ.· ℕ₊₁→ℤ d / b ·₊₁ (f ·₊₁ d) ]
            ≡[ i ]⟨ [ (g (a , b) (e , f)) ℤ.· ℕ₊₁→ℤ d / ·₊₁-assoc b f d i ] ⟩
          [ (g (a , b) (e , f)) ℤ.· ℕ₊₁→ℤ d / (b ·₊₁ f) ·₊₁ d ]
            ≡⟨ ·CancelR d ⟩
          [ g (a , b) (e , f) / b ·₊₁ f ] ∎

onCommonDenomSym :
  (g : ℤ × ℕ₊₁ → ℤ × ℕ₊₁ → ℤ)
  (g-sym : ∀ x y → g x y ≡ g y x)
  (g-eql : ∀ ((a , b) (c , d) (e , f) : ℤ × ℕ₊₁) (p : a ℤ.· ℕ₊₁→ℤ d ≡ c ℤ.· ℕ₊₁→ℤ b)
           → ℕ₊₁→ℤ d ℤ.· (g (a , b) (e , f)) ≡ ℕ₊₁→ℤ b ℤ.· (g (c , d) (e , f)))
  → ℚ → ℚ → ℚ
onCommonDenomSym g g-sym g-eql = onCommonDenom g g-eql q-eqr
  where abstract
        q-eqr : ∀ ((a , b) (c , d) (e , f) : ℤ × ℕ₊₁) (p : c ℤ.· ℕ₊₁→ℤ f ≡ e ℤ.· ℕ₊₁→ℤ d)
                → (g (a , b) (c , d)) ℤ.· ℕ₊₁→ℤ f ≡ (g (a , b) (e , f)) ℤ.· ℕ₊₁→ℤ d
        q-eqr (a , b) (c , d) (e , f) p =
          (g (a , b) (c , d)) ℤ.· ℕ₊₁→ℤ f ≡[ i ]⟨ ℤ.·Comm (g-sym (a , b) (c , d) i) (ℕ₊₁→ℤ f) i ⟩
          ℕ₊₁→ℤ f ℤ.· (g (c , d) (a , b)) ≡⟨ g-eql (c , d) (e , f) (a , b) p ⟩
          ℕ₊₁→ℤ d ℤ.· (g (e , f) (a , b)) ≡[ i ]⟨ ℤ.·Comm (ℕ₊₁→ℤ d) (g-sym (e , f) (a , b) i) i ⟩
          (g (a , b) (e , f)) ℤ.· ℕ₊₁→ℤ d ∎

onCommonDenomSym-comm : ∀ {g} g-sym {g-eql} (x y : ℚ)
                        → onCommonDenomSym g g-sym g-eql x y ≡
                          onCommonDenomSym g g-sym g-eql y x
onCommonDenomSym-comm g-sym = SetQuotient.elimProp2 (λ _ _ → isSetℚ _ _)
  (λ { (a , b) (c , d) i → [ g-sym (a , b) (c , d) i / ·₊₁-comm b d i ] })


-- basic arithmetic operations on ℚ

infixl 6 _+_
infixl 7 _·_

private abstract
  lem₁ : ∀ a b c d e (p : a ℤ.· b ≡ c ℤ.· d) → b ℤ.· (a ℤ.· e) ≡ d ℤ.· (c ℤ.· e)
  lem₁ a b c d e p =   ℤ.·Assoc b a e
                     ∙ cong (ℤ._· e) (ℤ.·Comm b a ∙ p ∙ ℤ.·Comm c d)
                     ∙ sym (ℤ.·Assoc d c e)

  lem₂ : ∀ a b c → a ℤ.· (b ℤ.· c) ≡ c ℤ.· (b ℤ.· a)
  lem₂ a b c =   cong (a ℤ.·_) (ℤ.·Comm b c) ∙ ℤ.·Assoc a c b
               ∙ cong (ℤ._· b) (ℤ.·Comm a c) ∙ sym (ℤ.·Assoc c a b)
               ∙ cong (c ℤ.·_) (ℤ.·Comm a b)

min : ℚ → ℚ → ℚ
min = onCommonDenomSym
  (λ { (a , b) (c , d) → ℤ.min (a ℤ.· ℕ₊₁→ℤ d) (c ℤ.· ℕ₊₁→ℤ b) })
  (λ { (a , b) (c , d) → ℤ.minComm (a ℤ.· ℕ₊₁→ℤ d) (c ℤ.· ℕ₊₁→ℤ b) })
   eq
  where abstract
    eq : ((a , b) (c , d) (e , f) : ℤ × ℕ₊₁) (p : a ℤ.· ℕ₊₁→ℤ d ≡ c ℤ.· ℕ₊₁→ℤ b)
       → ℕ₊₁→ℤ d ℤ.· ℤ.min (a ℤ.· ℕ₊₁→ℤ f) (e ℤ.· ℕ₊₁→ℤ b)
       ≡ ℕ₊₁→ℤ b ℤ.· ℤ.min (c ℤ.· ℕ₊₁→ℤ f) (e ℤ.· ℕ₊₁→ℤ d)
    eq (a , b) (c , d) (e , f) p =
      ℕ₊₁→ℤ d ℤ.· ℤ.min (a ℤ.· ℕ₊₁→ℤ f)
                         (e ℤ.· ℕ₊₁→ℤ b)
            ≡⟨ ℤ.·DistPosRMin (ℕ₊₁→ℕ d)
                              (a ℤ.· ℕ₊₁→ℤ f)
                              (e ℤ.· ℕ₊₁→ℤ b) ⟩
      ℤ.min (ℕ₊₁→ℤ d ℤ.· (a ℤ.· ℕ₊₁→ℤ f))
            (ℕ₊₁→ℤ d ℤ.· (e ℤ.· ℕ₊₁→ℤ b))
            ≡⟨ cong₂ ℤ.min (ℤ.·Assoc (ℕ₊₁→ℤ d) a (ℕ₊₁→ℤ f))
                           (ℤ.·Assoc (ℕ₊₁→ℤ d) e (ℕ₊₁→ℤ b)) ⟩
      ℤ.min (ℕ₊₁→ℤ d ℤ.· a ℤ.· ℕ₊₁→ℤ f)
            (ℕ₊₁→ℤ d ℤ.· e ℤ.· ℕ₊₁→ℤ b)
            ≡⟨ cong₂ ℤ.min (cong (ℤ._· ℕ₊₁→ℤ f)
                                 (ℤ.·Comm (ℕ₊₁→ℤ d) a ∙
                                  p ∙
                                  ℤ.·Comm c (ℕ₊₁→ℤ b)) ∙
                                  sym (ℤ.·Assoc (ℕ₊₁→ℤ b) c (ℕ₊₁→ℤ f)))
                           (cong (ℤ._· ℕ₊₁→ℤ b)
                                 (ℤ.·Comm (ℕ₊₁→ℤ d) e) ∙
                                 ℤ.·Comm (e ℤ.· ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b)) ⟩
      ℤ.min (ℕ₊₁→ℤ b ℤ.· (c ℤ.· ℕ₊₁→ℤ f))
            (ℕ₊₁→ℤ b ℤ.· (e ℤ.· ℕ₊₁→ℤ d))
            ≡⟨ sym (ℤ.·DistPosRMin (ℕ₊₁→ℕ b)
                                   (c ℤ.· ℕ₊₁→ℤ f)
                                   (e ℤ.· ℕ₊₁→ℤ d)) ⟩
      ℕ₊₁→ℤ b ℤ.· ℤ.min (c ℤ.· ℕ₊₁→ℤ f)
                         (e ℤ.· ℕ₊₁→ℤ d) ∎

max : ℚ → ℚ → ℚ
max = onCommonDenomSym
  (λ { (a , b) (c , d) → ℤ.max (a ℤ.· ℕ₊₁→ℤ d) (c ℤ.· ℕ₊₁→ℤ b) })
  (λ { (a , b) (c , d) → ℤ.maxComm (a ℤ.· ℕ₊₁→ℤ d) (c ℤ.· ℕ₊₁→ℤ b) })
   eq
  where abstract
    eq : ((a , b) (c , d) (e , f) : ℤ × ℕ₊₁) (p : a ℤ.· ℕ₊₁→ℤ d ≡ c ℤ.· ℕ₊₁→ℤ b)
       → ℕ₊₁→ℤ d ℤ.· ℤ.max (a ℤ.· ℕ₊₁→ℤ f) (e ℤ.· ℕ₊₁→ℤ b)
       ≡ ℕ₊₁→ℤ b ℤ.· ℤ.max (c ℤ.· ℕ₊₁→ℤ f) (e ℤ.· ℕ₊₁→ℤ d)
    eq (a , b) (c , d) (e , f) p =
      ℕ₊₁→ℤ d ℤ.· ℤ.max (a ℤ.· ℕ₊₁→ℤ f)
                         (e ℤ.· ℕ₊₁→ℤ b)
            ≡⟨ ℤ.·DistPosRMax (ℕ₊₁→ℕ d)
                              (a ℤ.· ℕ₊₁→ℤ f)
                              (e ℤ.· ℕ₊₁→ℤ b) ⟩
      ℤ.max (ℕ₊₁→ℤ d ℤ.· (a ℤ.· ℕ₊₁→ℤ f))
            (ℕ₊₁→ℤ d ℤ.· (e ℤ.· ℕ₊₁→ℤ b))
            ≡⟨ cong₂ ℤ.max (ℤ.·Assoc (ℕ₊₁→ℤ d) a (ℕ₊₁→ℤ f))
                           (ℤ.·Assoc (ℕ₊₁→ℤ d) e (ℕ₊₁→ℤ b)) ⟩
      ℤ.max (ℕ₊₁→ℤ d ℤ.· a ℤ.· ℕ₊₁→ℤ f)
            (ℕ₊₁→ℤ d ℤ.· e ℤ.· ℕ₊₁→ℤ b)
            ≡⟨ cong₂ ℤ.max (cong (ℤ._· ℕ₊₁→ℤ f)
                                 (ℤ.·Comm (ℕ₊₁→ℤ d) a ∙
                                  p ∙
                                  ℤ.·Comm c (ℕ₊₁→ℤ b)) ∙
                                  sym (ℤ.·Assoc (ℕ₊₁→ℤ b) c (ℕ₊₁→ℤ f)))
                           (cong (ℤ._· ℕ₊₁→ℤ b)
                                 (ℤ.·Comm (ℕ₊₁→ℤ d) e) ∙
                                 ℤ.·Comm (e ℤ.· ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b)) ⟩
      ℤ.max (ℕ₊₁→ℤ b ℤ.· (c ℤ.· ℕ₊₁→ℤ f))
            (ℕ₊₁→ℤ b ℤ.· (e ℤ.· ℕ₊₁→ℤ d))
            ≡⟨ sym (ℤ.·DistPosRMax (ℕ₊₁→ℕ b)
                                   (c ℤ.· ℕ₊₁→ℤ f)
                                   (e ℤ.· ℕ₊₁→ℤ d)) ⟩
      ℕ₊₁→ℤ b ℤ.· ℤ.max (c ℤ.· ℕ₊₁→ℤ f)
                         (e ℤ.· ℕ₊₁→ℤ d) ∎

minComm : ∀ x y → min x y ≡ min y x
minComm = onCommonDenomSym-comm
  (λ { (a , b) (c , d) → ℤ.minComm (a ℤ.· ℕ₊₁→ℤ d) (c ℤ.· ℕ₊₁→ℤ b) })

maxComm : ∀ x y → max x y ≡ max y x
maxComm = onCommonDenomSym-comm
  (λ { (a , b) (c , d) → ℤ.maxComm (a ℤ.· ℕ₊₁→ℤ d) (c ℤ.· ℕ₊₁→ℤ b) })

minIdem : ∀ x → min x x ≡ x
minIdem = SetQuotient.elimProp (λ _ → isSetℚ _ _)
  λ { (a , b) → eq/ (ℤ.min (a ℤ.· ℕ₊₁→ℤ b) (a ℤ.· ℕ₊₁→ℤ b) , b ·₊₁ b) (a , b)
                    (cong (ℤ._· ℕ₊₁→ℤ b) (ℤ.minIdem (a ℤ.· ℕ₊₁→ℤ b)) ∙
                     sym (ℤ.·Assoc a (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ b)) ∙
                     cong (a ℤ.·_) (sym (pos·pos (ℕ₊₁→ℕ b) (ℕ₊₁→ℕ b)))) }

maxIdem : ∀ x → max x x ≡ x
maxIdem = SetQuotient.elimProp (λ _ → isSetℚ _ _)
  λ { (a , b) → eq/ (ℤ.max (a ℤ.· ℕ₊₁→ℤ b) (a ℤ.· ℕ₊₁→ℤ b) , b ·₊₁ b) (a , b)
                    (cong (ℤ._· ℕ₊₁→ℤ b) (ℤ.maxIdem (a ℤ.· ℕ₊₁→ℤ b)) ∙
                     sym (ℤ.·Assoc a (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ b)) ∙
                     cong (a ℤ.·_) (sym (pos·pos (ℕ₊₁→ℕ b) (ℕ₊₁→ℕ b)))) }

minAssoc : ∀ x y z → min x (min y z) ≡ min (min x y) z
minAssoc = SetQuotient.elimProp3 (λ _ _ _ → isSetℚ _ _)
  λ { (a , b) (c , d) (e , f) i
    → [ (cong₂ ℤ.min
               (cong (a ℤ.·_) (pos·pos (ℕ₊₁→ℕ d) (ℕ₊₁→ℕ f))
               ∙ ℤ.·Assoc a (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ f))
               (ℤ.·DistPosLMin (c ℤ.· ℕ₊₁→ℤ f)
                               (e ℤ.· ℕ₊₁→ℤ d)
                               (ℕ₊₁→ℕ b)
               ∙ cong₂ ℤ.min (sym (ℤ.·Assoc c (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ b))
                             ∙ cong (c ℤ.·_) (ℤ.·Comm (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ b))
                             ∙ ℤ.·Assoc c (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ f))
                             (sym (ℤ.·Assoc e (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b))
                             ∙ cong (e ℤ.·_) (ℤ.·Comm (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b)
                                             ∙ sym (pos·pos (ℕ₊₁→ℕ b) (ℕ₊₁→ℕ d)))))
        ∙ ℤ.minAssoc (a ℤ.· ℕ₊₁→ℤ d ℤ.· ℕ₊₁→ℤ f)
                     (c ℤ.· ℕ₊₁→ℤ b ℤ.· ℕ₊₁→ℤ f)
                     (e ℤ.· ℕ₊₁→ℤ (b ·₊₁ d))
        ∙ cong (λ x → ℤ.min x (e ℤ.· ℕ₊₁→ℤ (b ·₊₁ d)))
               (sym (ℤ.·DistPosLMin (a ℤ.· ℕ₊₁→ℤ d)
                                    (c ℤ.· ℕ₊₁→ℤ b)
                                    (ℕ₊₁→ℕ f)))) i / ·₊₁-assoc b d f i ] }

maxAssoc : ∀ x y z → max x (max y z) ≡ max (max x y) z
maxAssoc = SetQuotient.elimProp3 (λ _ _ _ → isSetℚ _ _)
  λ { (a , b) (c , d) (e , f) i
    → [ (cong₂ ℤ.max
               (cong (a ℤ.·_) (pos·pos (ℕ₊₁→ℕ d) (ℕ₊₁→ℕ f))
               ∙ ℤ.·Assoc a (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ f))
               (ℤ.·DistPosLMax (c ℤ.· ℕ₊₁→ℤ f)
                               (e ℤ.· ℕ₊₁→ℤ d)
                               (ℕ₊₁→ℕ b)
               ∙ cong₂ ℤ.max (sym (ℤ.·Assoc c (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ b))
                             ∙ cong (c ℤ.·_) (ℤ.·Comm (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ b))
                             ∙ ℤ.·Assoc c (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ f))
                             (sym (ℤ.·Assoc e (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b))
                             ∙ cong (e ℤ.·_) (ℤ.·Comm (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b)
                                             ∙ sym (pos·pos (ℕ₊₁→ℕ b) (ℕ₊₁→ℕ d)))))
        ∙ ℤ.maxAssoc (a ℤ.· ℕ₊₁→ℤ d ℤ.· ℕ₊₁→ℤ f)
                     (c ℤ.· ℕ₊₁→ℤ b ℤ.· ℕ₊₁→ℤ f)
                     (e ℤ.· ℕ₊₁→ℤ (b ·₊₁ d))
        ∙ cong (λ x → ℤ.max x (e ℤ.· ℕ₊₁→ℤ (b ·₊₁ d)))
               (sym (ℤ.·DistPosLMax (a ℤ.· ℕ₊₁→ℤ d)
                                    (c ℤ.· ℕ₊₁→ℤ b)
                                    (ℕ₊₁→ℕ f)))) i / ·₊₁-assoc b d f i ] }

minAbsorbLMax : ∀ x y → min x (max x y) ≡ x
minAbsorbLMax = SetQuotient.elimProp2 (λ _ _ → isSetℚ _ _)
  λ { (a , b) (c , d)
    → eq/ (ℤ.min (a ℤ.· ℕ₊₁→ℤ (b ·₊₁ d))
                 (ℤ.max (a ℤ.· ℕ₊₁→ℤ d)
                        (c ℤ.· ℕ₊₁→ℤ b)
           ℤ.· ℕ₊₁→ℤ b) ,
           b ·₊₁ (b ·₊₁ d))
          (a , b)
          (ℤ.min (a ℤ.· ℕ₊₁→ℤ (b ·₊₁ d))
                 (ℤ.max (a ℤ.· ℕ₊₁→ℤ d)
                        (c ℤ.· ℕ₊₁→ℤ b)
                         ℤ.· ℕ₊₁→ℤ b)
           ℤ.· ℕ₊₁→ℤ b ≡⟨ cong (λ x → ℤ.min (a ℤ.· ℕ₊₁→ℤ (b ·₊₁ d)) x
                                  ℤ.· ℕ₊₁→ℤ b)
                                (ℤ.·DistPosLMax (a ℤ.· ℕ₊₁→ℤ d) _ (ℕ₊₁→ℕ b)) ⟩
           ℤ.min (a ℤ.· ℕ₊₁→ℤ (b ·₊₁ d))
          (ℤ.max (a ℤ.· ℕ₊₁→ℤ d ℤ.· ℕ₊₁→ℤ b)
                 (c ℤ.· ℕ₊₁→ℤ b ℤ.· ℕ₊₁→ℤ b))
           ℤ.· ℕ₊₁→ℤ b ≡⟨ cong (λ x → ℤ.min (a ℤ.· ℕ₊₁→ℤ (b ·₊₁ d))
                                (ℤ.max x (c ℤ.· ℕ₊₁→ℤ b ℤ.· ℕ₊₁→ℤ b))
                                 ℤ.· ℕ₊₁→ℤ b)
                                (sym (ℤ.·Assoc a (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b)) ∙
                                 cong (a ℤ.·_) (sym (pos·pos (ℕ₊₁→ℕ d) (ℕ₊₁→ℕ b)) ∙
                                                cong ℕ₊₁→ℤ (·₊₁-comm d b))) ⟩
           ℤ.min (a ℤ.· ℕ₊₁→ℤ (b ·₊₁ d))
          (ℤ.max (a ℤ.· ℕ₊₁→ℤ (b ·₊₁ d))
                 (c ℤ.· ℕ₊₁→ℤ b ℤ.· ℕ₊₁→ℤ b))
           ℤ.· ℕ₊₁→ℤ b ≡⟨ cong (ℤ._· ℕ₊₁→ℤ b)
                                (ℤ.minAbsorbLMax (a ℤ.· ℕ₊₁→ℤ (b ·₊₁ d)) _) ⟩
           a ℤ.· ℕ₊₁→ℤ (b ·₊₁ d) ℤ.· ℕ₊₁→ℤ b
                 ≡⟨ sym (ℤ.·Assoc a (ℕ₊₁→ℤ (b ·₊₁ d)) (ℕ₊₁→ℤ b)) ∙
                    cong (a ℤ.·_) (sym (pos·pos (ℕ₊₁→ℕ (b ·₊₁ d)) (ℕ₊₁→ℕ b)) ∙
                                   cong ℕ₊₁→ℤ (·₊₁-comm (b ·₊₁ d) b)) ⟩
           a ℤ.· ℕ₊₁→ℤ (b ·₊₁ (b ·₊₁ d)) ∎) }

maxAbsorbLMin : ∀ x y → max x (min x y) ≡ x
maxAbsorbLMin = SetQuotient.elimProp2 (λ _ _ → isSetℚ _ _)
  λ { (a , b) (c , d)
    → eq/ (ℤ.max (a ℤ.· ℕ₊₁→ℤ (b ·₊₁ d))
                 (ℤ.min (a ℤ.· ℕ₊₁→ℤ d)
                        (c ℤ.· ℕ₊₁→ℤ b)
                  ℤ.· ℕ₊₁→ℤ b) ,
                  b ·₊₁ (b ·₊₁ d))
                 (a , b)
          (ℤ.max (a ℤ.· ℕ₊₁→ℤ (b ·₊₁ d))
                 (ℤ.min (a ℤ.· ℕ₊₁→ℤ d)
                        (c ℤ.· ℕ₊₁→ℤ b)
                  ℤ.· ℕ₊₁→ℤ b)
           ℤ.· ℕ₊₁→ℤ b ≡⟨ cong (λ x → ℤ.max (a ℤ.· ℕ₊₁→ℤ (b ·₊₁ d)) x
                                  ℤ.· ℕ₊₁→ℤ b)
                                (ℤ.·DistPosLMin (a ℤ.· ℕ₊₁→ℤ d) _ (ℕ₊₁→ℕ b)) ⟩
           ℤ.max (a ℤ.· ℕ₊₁→ℤ (b ·₊₁ d))
                 (ℤ.min (a ℤ.· ℕ₊₁→ℤ d ℤ.· ℕ₊₁→ℤ b)
                        (c ℤ.· ℕ₊₁→ℤ b ℤ.· ℕ₊₁→ℤ b))
           ℤ.· ℕ₊₁→ℤ b ≡⟨ cong (λ x → ℤ.max (a ℤ.· ℕ₊₁→ℤ (b ·₊₁ d))
                                             (ℤ.min x (c ℤ.· ℕ₊₁→ℤ b ℤ.· ℕ₊₁→ℤ b))
                                       ℤ.· ℕ₊₁→ℤ b)
                                (sym (ℤ.·Assoc a (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b)) ∙
                                 cong (a ℤ.·_) (sym (pos·pos (ℕ₊₁→ℕ d) (ℕ₊₁→ℕ b)) ∙
                                                cong ℕ₊₁→ℤ (·₊₁-comm d b))) ⟩
           ℤ.max (a ℤ.· ℕ₊₁→ℤ (b ·₊₁ d))
                 (ℤ.min (a ℤ.· ℕ₊₁→ℤ (b ·₊₁ d))
                        (c ℤ.· ℕ₊₁→ℤ b ℤ.· ℕ₊₁→ℤ b))
           ℤ.· ℕ₊₁→ℤ b ≡⟨ cong (ℤ._· ℕ₊₁→ℤ b)
                                (ℤ.maxAbsorbLMin (a ℤ.· ℕ₊₁→ℤ (b ·₊₁ d)) _) ⟩
           a ℤ.· ℕ₊₁→ℤ (b ·₊₁ d) ℤ.· ℕ₊₁→ℤ b
             ≡⟨ sym (ℤ.·Assoc a (ℕ₊₁→ℤ (b ·₊₁ d)) (ℕ₊₁→ℤ b)) ∙
                cong (a ℤ.·_) (sym (pos·pos (ℕ₊₁→ℕ (b ·₊₁ d)) (ℕ₊₁→ℕ b)) ∙
                               cong ℕ₊₁→ℤ (·₊₁-comm (b ·₊₁ d) b)) ⟩
           a ℤ.· ℕ₊₁→ℤ (b ·₊₁ (b ·₊₁ d)) ∎) }

_+_ : ℚ → ℚ → ℚ
_+_ = onCommonDenomSym
  (λ { (a , b) (c , d) → a ℤ.· (ℕ₊₁→ℤ d) ℤ.+ c ℤ.· (ℕ₊₁→ℤ b) })
  (λ { (a , b) (c , d) → ℤ.+Comm (a ℤ.· (ℕ₊₁→ℤ d)) (c ℤ.· (ℕ₊₁→ℤ b)) })
   eq
  where abstract
    eq : ((a , b) (c , d) (e , f) : ℤ × ℕ₊₁) (p : a ℤ.· ℕ₊₁→ℤ d ≡ c ℤ.· ℕ₊₁→ℤ b)
       → ℕ₊₁→ℤ d ℤ.· (a ℤ.· ℕ₊₁→ℤ f ℤ.+ e ℤ.· ℕ₊₁→ℤ b)
       ≡ ℕ₊₁→ℤ b ℤ.· (c ℤ.· ℕ₊₁→ℤ f ℤ.+ e ℤ.· ℕ₊₁→ℤ d)
    eq (a , b) (c , d) (e , f) p =
      ℕ₊₁→ℤ d ℤ.· (a ℤ.· ℕ₊₁→ℤ f ℤ.+ e ℤ.· ℕ₊₁→ℤ b)
        ≡⟨ ℤ.·DistR+ (ℕ₊₁→ℤ d) (a ℤ.· ℕ₊₁→ℤ f) (e ℤ.· ℕ₊₁→ℤ b) ⟩
      ℕ₊₁→ℤ d ℤ.· (a ℤ.· ℕ₊₁→ℤ f) ℤ.+ ℕ₊₁→ℤ d ℤ.· (e ℤ.· ℕ₊₁→ℤ b)
        ≡[ i ]⟨ lem₁ a (ℕ₊₁→ℤ d) c (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ f) p i ℤ.+ lem₂ (ℕ₊₁→ℤ d) e (ℕ₊₁→ℤ b) i ⟩
      ℕ₊₁→ℤ b ℤ.· (c ℤ.· ℕ₊₁→ℤ f) ℤ.+ ℕ₊₁→ℤ b ℤ.· (e ℤ.· ℕ₊₁→ℤ d)
        ≡⟨ sym (ℤ.·DistR+ (ℕ₊₁→ℤ b) (c ℤ.· ℕ₊₁→ℤ f) (e ℤ.· ℕ₊₁→ℤ d)) ⟩
      ℕ₊₁→ℤ b ℤ.· (c ℤ.· ℕ₊₁→ℤ f ℤ.+ e ℤ.· ℕ₊₁→ℤ d) ∎

+Comm : ∀ x y → x + y ≡ y + x
+Comm = onCommonDenomSym-comm
  (λ { (a , b) (c , d) → ℤ.+Comm (a ℤ.· (ℕ₊₁→ℤ d)) (c ℤ.· (ℕ₊₁→ℤ b)) })

+IdL : ∀ x → 0 + x ≡ x
+IdL = SetQuotient.elimProp (λ _ → isSetℚ _ _)
  λ { (a , b) i → [ ((cong (ℤ._+ a ℤ.· ℕ₊₁→ℤ 1) (ℤ.·AnnihilL (ℕ₊₁→ℤ b))
                    ∙ sym (pos0+ (a ℤ.· ℕ₊₁→ℤ 1)))
                    ∙ ℤ.·IdR a) i / ·₊₁-identityˡ b i ] }

+IdR : ∀ x → x + 0 ≡ x
+IdR x = +Comm x _ ∙ +IdL x

+Assoc : ∀ x y z → x + (y + z) ≡ (x + y) + z
+Assoc = SetQuotient.elimProp3 (λ _ _ _ → isSetℚ _ _)
  (λ { (a , b) (c , d) (e , f) i
    → [ (cong (λ x → a ℤ.· x ℤ.+ (c ℤ.· ℕ₊₁→ℤ f ℤ.+ e ℤ.· ℕ₊₁→ℤ d) ℤ.· ℕ₊₁→ℤ b)
              (pos·pos (ℕ₊₁→ℕ d) (ℕ₊₁→ℕ f))
       ∙ eq a (ℕ₊₁→ℤ b) c (ℕ₊₁→ℤ d) e (ℕ₊₁→ℤ f)
       ∙ cong (λ x → (a ℤ.· ℕ₊₁→ℤ d ℤ.+ c ℤ.· ℕ₊₁→ℤ b) ℤ.· ℕ₊₁→ℤ f ℤ.+ e ℤ.· x)
              (sym (pos·pos (ℕ₊₁→ℕ b) (ℕ₊₁→ℕ d)))) i / ·₊₁-assoc b d f i ] })
  where eq₁ : ∀ a b c → (a ℤ.· b) ℤ.· c ≡ a ℤ.· (c ℤ.· b)
        eq₁ a b c = sym (ℤ.·Assoc a b c) ∙ cong (a ℤ.·_) (ℤ.·Comm b c)
        eq₂ : ∀ a b c → (a ℤ.· b) ℤ.· c ≡ (a ℤ.· c) ℤ.· b
        eq₂ a b c = eq₁ a b c ∙ ℤ.·Assoc a c b

        eq : ∀ a b c d e f → Path ℤ _ _
        eq a b c d e f =
          a ℤ.· (d ℤ.· f) ℤ.+ (c ℤ.· f ℤ.+ e ℤ.· d) ℤ.· b
            ≡[ i ]⟨ a ℤ.· (d ℤ.· f) ℤ.+ ℤ.·DistL+ (c ℤ.· f) (e ℤ.· d) b i ⟩
          a ℤ.· (d ℤ.· f) ℤ.+ ((c ℤ.· f) ℤ.· b ℤ.+ (e ℤ.· d) ℤ.· b)
            ≡[ i ]⟨ ℤ.+Assoc (ℤ.·Assoc a d f i) (eq₂ c f b i) (eq₁ e d b i) i ⟩
          ((a ℤ.· d) ℤ.· f ℤ.+ (c ℤ.· b) ℤ.· f) ℤ.+ e ℤ.· (b ℤ.· d)
            ≡[ i ]⟨ ℤ.·DistL+ (a ℤ.· d) (c ℤ.· b) f (~ i) ℤ.+ e ℤ.· (b ℤ.· d) ⟩
          (a ℤ.· d ℤ.+ c ℤ.· b) ℤ.· f ℤ.+ e ℤ.· (b ℤ.· d) ∎


_·_ : ℚ → ℚ → ℚ
_·_ = onCommonDenomSym
  (λ { (a , _) (c , _) → a ℤ.· c })
  (λ { (a , _) (c , _) → ℤ.·Comm a c })
  (λ { (a , b) (c , d) (e , _) p → lem₁ a (ℕ₊₁→ℤ d) c (ℕ₊₁→ℤ b) e p })

·Comm : ∀ x y → x · y ≡ y · x
·Comm = onCommonDenomSym-comm (λ { (a , _) (c , _) → ℤ.·Comm a c })

·IdL : ∀ x → 1 · x ≡ x
·IdL = SetQuotient.elimProp (λ _ → isSetℚ _ _)
  (λ { (a , b) i → [ ℤ.·IdL a i / ·₊₁-identityˡ b i ] })

·IdR : ∀ x → x · 1 ≡ x
·IdR = SetQuotient.elimProp (λ _ → isSetℚ _ _)
  (λ { (a , b) i → [ ℤ.·IdR a i / ·₊₁-identityʳ b i ] })

·AnnihilL : ∀ x → 0 · x ≡ 0
·AnnihilL = SetQuotient.elimProp (λ _ → isSetℚ _ _)
  (λ { (a , b) → (λ i → [ p a b i / 1 ·₊₁ b ]) ∙ ·CancelR b })
  where p : ∀ a b → 0 ℤ.· a ≡ 0 ℤ.· ℕ₊₁→ℤ b
        p a b = ℤ.·AnnihilL a ∙ sym (ℤ.·AnnihilL (ℕ₊₁→ℤ b))

·AnnihilR : ∀ x → x · 0 ≡ 0
·AnnihilR = SetQuotient.elimProp (λ _ → isSetℚ _ _)
  (λ { (a , b) → (λ i → [ p a b i / b ·₊₁ 1 ]) ∙ ·CancelL b })
  where p : ∀ a b → a ℤ.· 0 ≡ ℕ₊₁→ℤ b ℤ.· 0
        p a b = ℤ.·AnnihilR a ∙ sym (ℤ.·AnnihilR (ℕ₊₁→ℤ b))

·Assoc : ∀ x y z → x · (y · z) ≡ (x · y) · z
·Assoc = SetQuotient.elimProp3 (λ _ _ _ → isSetℚ _ _)
  (λ { (a , b) (c , d) (e , f) i → [ ℤ.·Assoc a c e i / ·₊₁-assoc b d f i ] })

·DistL+ : ∀ x y z → x · (y + z) ≡ (x · y) + (x · z)
·DistL+ = SetQuotient.elimProp3 (λ _ _ _ → isSetℚ _ _)
  (λ { (a , b) (c , d) (e , f) → sym (eq a b c d e f)})
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

        lemℤ   = lem ℤ._·_ ℤ.·Comm ℤ.·Assoc
        lemℕ₊₁ = lem _·₊₁_ ·₊₁-comm ·₊₁-assoc

        eq : ∀ a b c d e f →
               [ (a ℤ.· c) ℤ.· ℕ₊₁→ℤ (b ·₊₁ f) ℤ.+ (a ℤ.· e) ℤ.· ℕ₊₁→ℤ (b ·₊₁ d)
                 / (b ·₊₁ d) ·₊₁ (b ·₊₁ f) ]
             ≡ [ a ℤ.· (c ℤ.· ℕ₊₁→ℤ f ℤ.+ e ℤ.· ℕ₊₁→ℤ d)
                / b ·₊₁ (d ·₊₁ f) ]
        eq a b c d e f =
          (λ i → [ (cong (a ℤ.· c ℤ.·_) (pos·pos (ℕ₊₁→ℕ b) (ℕ₊₁→ℕ f))
                 ∙ (lemℤ a c (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ f))) i
                   ℤ.+
                   (cong (a ℤ.· e ℤ.·_) (pos·pos (ℕ₊₁→ℕ b) (ℕ₊₁→ℕ d))
                 ∙ (lemℤ a e (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ d))) i
                   / lemℕ₊₁ b d b f i ]) ∙
          (λ i → [ (sym (ℤ.·DistL+ (a ℤ.· (c ℤ.· ℕ₊₁→ℤ f)) (a ℤ.· (e ℤ.· ℕ₊₁→ℤ d)) (ℕ₊₁→ℤ b))) i
                   / (b ·₊₁ (d ·₊₁ f)) ·₊₁ b ]) ∙
          ·CancelR {a ℤ.· (c ℤ.· ℕ₊₁→ℤ f) ℤ.+ a ℤ.· (e ℤ.· ℕ₊₁→ℤ d)} {b ·₊₁ (d ·₊₁ f)} b ∙
          (λ i → [ (sym (ℤ.·DistR+ a (c ℤ.· ℕ₊₁→ℤ f) (e ℤ.· ℕ₊₁→ℤ d))) i
                   / b ·₊₁ (d ·₊₁ f) ])

·DistR+ : ∀ x y z → (x + y) · z ≡ (x · z) + (y · z)
·DistR+ x y z = sym ((λ i → ·Comm x z i + ·Comm y z i) ∙ (sym (·DistL+ z x y)) ∙ ·Comm z (x + y))


-_ : ℚ → ℚ
- x = -1 · x

-Invol : ∀ x → - - x ≡ x
-Invol x = ·Assoc -1 -1 x ∙ ·IdL x

negateEquiv : ℚ ≃ ℚ
negateEquiv = isoToEquiv (iso -_ -_ -Invol -Invol)

negateEq : ℚ ≡ ℚ
negateEq = ua negateEquiv

+InvL : ∀ x → (- x) + x ≡ 0
+InvL x = (λ i → (-1 · x) + ·IdL x (~ i)) ∙ (sym (·DistR+ -1 1 x)) ∙ ·AnnihilL x

_-_ : ℚ → ℚ → ℚ
x - y = x + (- y)

+InvR : ∀ x → x - x ≡ 0
+InvR x = +Comm x (- x) ∙ +InvL x

+CancelL : ∀ x y z → x + y ≡ x + z → y ≡ z
+CancelL x y z p = sym (q y) ∙ cong ((- x) +_) p ∙ q z
  where q : ∀ y → (- x) + (x + y) ≡ y
        q y = +Assoc (- x) x y ∙ cong (_+ y) (+InvL x) ∙ +IdL y

+CancelR : ∀ x y z → x + y ≡ z + y → x ≡ z
+CancelR x y z p = +CancelL y x z (+Comm y x ∙ p ∙ +Comm z y)

module Cubical.Data.Rationals.MoreRationals.SigmaQ.Properties where

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat as ℕ using (ℕ; suc; zero; predℕ)
open import Cubical.Data.Nat.GCD as ℕ
open import Cubical.Data.Nat.Coprime
open import Cubical.Data.Nat.Properties hiding (≢0→NonZero)
open import Cubical.Data.NatPlusOne.PropertiesWithInt
  using (ℕ₊₁→ℤ; ·ℕ₊₁→ℤ-distr)
open import Cubical.Foundations.Prelude
open import Cubical.Relation.Nullary
open import Cubical.Data.Int as ℤ
  using (ℤ; pos; negsuc; isIntegralℤ; injPos)
open import Cubical.Data.Int.GCD as ℤ
open import Cubical.Data.NatPlusOne as ℕ₊₁
  using (1+_; _·₊₁_; ℕ₊₁; ℕ₊₁→ℕ; ·₊₁-comm; -1+_;
    ·₊₁-identityʳ; ·₊₁-identityˡ ; ·₊₁-assoc; ·₊₁-interchange; ·₊₁-assoc4)
open import Cubical.Data.Rationals.MoreRationals.SigmaQ.Base

private
  converse : {ℓ : Level} {a b : Type ℓ} →
    (a → b) → ¬ b → ¬ a
  converse = λ z z₁ z₂ → z₁ (z z₂)

-- Operations on ℚ
infixl 6 _-_ _+_
infixl 7 _·_ _/_
infix  8 1/_

-- Addition/Subtraction
_+_ : ℚ → ℚ → ℚ
p + q = [ ((↥ p) ℤ.· (↧ q)) ℤ.+ ((↥ q) ℤ.· (↧ p)) , (↧₊₁ p) ·₊₁ (↧₊₁ q) ]

_-_ : ℚ → ℚ → ℚ
p - q = p + (- q)

-- Multiplication
_·_ : ℚ → ℚ → ℚ
p · q = [ (↥ p) ℤ.· (↥ q) , (↧₊₁ p) ·₊₁ (↧₊₁ q) ]

-- Reciprocal: requires a proof that the numerator is not zero
1/_ : (p : ℚ) → {{nz : NonZero p}} → ℚ
1/ ((p@(pos (suc n)) , d-1) , c) = (pos (suc d-1) , n) , symGCD c
1/ ((p@(negsuc n) , d-1) , c) = ((negsuc d-1) , n) , symGCD c

-- Divide
_/_ : (p : ℚ) → (q : ℚ) → {{nz : NonZero q}} → ℚ
p / q = p · (1/ q)

-------------------------------------------------
-- Preliminaries for _+_ and _·_

·[]CancelR : ∀ {a b} (c : ℕ₊₁) → [ a ℤ.· ℕ₊₁→ℤ c , b ·₊₁ c ] ≡ [ a , b ]
·[]CancelR {pos m}{n} c =
  (cong (λ x → [ x ,  n ·₊₁ c ]) (sym (ℤ.pos·pos m (ℕ₊₁→ℕ c)))) ∙
  ·CancelR-normalise (m , n) c
·[]CancelR {negsuc m}{n} c =
    (cong (λ a → [ a , n ·₊₁ c ])
    (ℤ.negsuc·pos m (ℕ.suc (c .ℕ₊₁.n))
  ∙ cong (λ a → ℤ.- a) (sym (ℤ.pos·pos (ℕ.suc m) (ℕ.suc (c .ℕ₊₁.n))))))
  ∙ (cong -_ (·CancelR-normalise ((ℕ.suc m) , n) c))

·[]Cancel : ∀ {a b x y} (c : ℕ₊₁) → (eq1 : x ≡ a ℤ.· ℕ₊₁→ℤ c) →
  (eq2 : y ≡ b ·₊₁ c) → [ x , y ] ≡ [ a , b ]
·[]Cancel {a}{b}{x}{y} c eq1 eq2 =
  cong₂ (λ x' y' → [ x' , y' ]) eq1 eq2 ∙ ·[]CancelR {a}{b} c

·[]CancelL : ∀ {a b} (c : ℕ₊₁) → [ ℕ₊₁→ℤ c ℤ.· a , c ·₊₁ b ] ≡ [ a , b ]
·[]CancelL {a}{b} c =
  ·[]Cancel {a}{b} {ℕ₊₁→ℤ c ℤ.· a}{c ·₊₁ b} c (ℤ.·Comm (ℕ₊₁→ℤ c) a) (·₊₁-comm c b)

·ᵘ-def : ∀ x y d d' → [ x , d ] · [ y , d' ] ≡ [ x ℤ.· y , d ·₊₁ d' ]
·ᵘ-def x y d d' =
  sym (·[]CancelR {step1 ℤ.· ((↥ p) ℤ.· (↥ q))} {step3 ·₊₁ ((↧₊₁ p) ·₊₁ (↧₊₁ q))} step4 ∙
       ·[]CancelL {(↥ p) ℤ.· (↥ q)}{(↧₊₁ p) ·₊₁ (↧₊₁ q)} step3) ∙
  cong₂ (λ u v → [ u , v ]) step5 step6
  where
    d-1 = -1+ d ; d-1' = -1+ d' ; p = [ x , 1+ d-1 ] ; q = [ y , 1+ d-1' ]
    x≡ = ↥·gcd-lemma x d-1 ; y≡ = ↥·gcd-lemma y d-1'
    step1 = ℕ₊₁→ℤ (1+ predℕ (ℕ.gcd (ℤ.abs x) (suc d-1)))
    step1' = pos (ℕ.gcd (ℤ.abs x) (suc d-1))
    step1≡1' = ℕ₊₁→ℤ-gcd-def (ℤ.abs x) d-1
    step3 = 1+ predℕ (ℕ.gcd (ℤ.abs x) (suc d-1))
    step2 = ℕ₊₁→ℤ (1+ predℕ (ℕ.gcd (ℤ.abs y) (suc d-1')))
    step2' = pos (ℕ.gcd (ℤ.abs y) (suc d-1'))
    step2≡2' = ℕ₊₁→ℤ-gcd-def (ℤ.abs y) d-1'
    step4 = 1+ (predℕ (ℕ.gcd (ℤ.abs y) (suc d-1')))
    step5 : (step1 ℤ.· ((↥ p) ℤ.· (↥ q))) ℤ.· step2 ≡ x ℤ.· y
    step5 = (cong₂ (λ u v → u ℤ.· ((↥ p) ℤ.· (↥ q)) ℤ.· v) step1≡1' step2≡2' ∙
      (ℤ.·-assoc4 step1' (↥ p) (↥ q) step2') ∙
      cong (λ u → u ℤ.· ((↥ q) ℤ.· step2')) (ℤ.·Comm step1' (↥ p)) ∙
      cong₂ (λ a b → a ℤ.· b) (sym x≡) (sym y≡))
    step6 = (·₊₁-assoc4 step3 (↧₊₁ p) (↧₊₁ q) step4) ∙
      cong (λ u → u ·₊₁ (↧₊₁ q ·₊₁ step4)) (·₊₁-comm step3 (↧₊₁ p)) ∙
      cong₂ (λ u v → u ·₊₁ v)
       (sym (↧₊₁·gcd-lemma x d-1)) (sym (↧₊₁·gcd-lemma y d-1'))

·ᵘ-def-cross : ∀ x y d d' → [ x , d ] · [ y , d' ] ≡ [ x ℤ.· y , d' ·₊₁ d ]
·ᵘ-def-cross x y d d' =
  ·ᵘ-def x y d d' ∙ cong (λ a → [ x ℤ.· y , a ]) (·₊₁-comm d d')

·[]CancelCrossR : ∀ x d d' → [ x , d ] · [ ℕ₊₁→ℤ d , d' ] ≡ [ x , d' ]
·[]CancelCrossR x d d' = ·ᵘ-def x (ℕ₊₁→ℤ d) d d' ∙
  cong (λ u → [ u ,  d ·₊₁ d' ]) (ℤ.·Comm x (ℕ₊₁→ℤ d)) ∙
  ·[]CancelL {x}{d'} d

·[]CancelCrossL : ∀ x d d' → [ ℕ₊₁→ℤ d , d' ] · [ x , d ] ≡ [ x , d' ]
·[]CancelCrossL x d d' = ·ᵘ-def (ℕ₊₁→ℤ d) x d' d ∙
  cong (λ u → [ u ,  d' ·₊₁ d ]) (ℤ.·Comm (ℕ₊₁→ℤ d) x) ∙
  ·[]CancelR {x}{d'} d

·[]IdR : ∀ x d → [ x , d ] · 1ℚ ≡ [ x , d ]
·[]IdR x d = ·ᵘ-def x (pos (suc zero)) d (1+ zero) ∙
  cong₂ (λ u v → [ u , v ]) (ℤ.·IdR x) (·₊₁-identityʳ d)

·[]IdL : ∀ x d → 1ℚ · [ x , d ] ≡ [ x , d ]
·[]IdL x d = ·ᵘ-def (pos (suc zero)) x (1+ zero) d ∙
  cong₂ (λ u v → [ u , v ]) (ℤ.·IdL x) (·₊₁-identityˡ d)

+ᵘ-def : ∀ x y d d' →
  [ x , d ] + [ y , d' ] ≡ [ (x ℤ.· ℕ₊₁→ℤ d') ℤ.+ (y ℤ.· ℕ₊₁→ℤ d) , d ·₊₁ d' ]
+ᵘ-def x y d d' = step1 ∙ cong₂ (λ u v → [ u , v ]) (step2 ∙ step3) step4
  where
    d-1 = -1+ d ; d-1' = -1+ d' ; p = [ x , 1+ d-1 ] ; q = [ y , 1+ d-1' ]
    over = ((↥ p) ℤ.· (↧ q)) ℤ.+ ((↥ q) ℤ.· (↧ p))
    under = (↧₊₁ p) ·₊₁ (↧₊₁ q)
    xy = pos (ℕ.gcd (ℤ.abs x) (suc d-1)) ℤ.· pos (ℕ.gcd (ℤ.abs y) (suc d-1'))
    step1 = sym (·[]CancelL (1+ predℕ (ℕ.gcd (ℤ.abs x) (suc d-1)) ·₊₁
      1+ predℕ (ℕ.gcd (ℤ.abs y) (suc d-1'))))
    step2 = cong (λ u → u  ℤ.· over)
      ((·ℕ₊₁→ℤ-distr (1+ predℕ (ℕ.gcd (ℤ.abs x) (suc d-1)))
       (1+ predℕ (ℕ.gcd (ℤ.abs y) (suc d-1')))) ∙
      (cong₂ (λ a b → a ℤ.· b)
       (ℕ₊₁→ℤ-gcd-def (ℤ.abs x) d-1) (ℕ₊₁→ℤ-gcd-def (ℤ.abs y) d-1')))
    step3 : xy ℤ.· over ≡ (x ℤ.· ℕ₊₁→ℤ d') ℤ.+ (y ℤ.· ℕ₊₁→ℤ d)
    step3 =
      ℤ.·DistR+ xy ((↥ p) ℤ.· (↧ q)) ((↥ q) ℤ.· (↧ p)) ∙
      cong₂ (λ u v → u ℤ.+ v)
       ((ℤ.·-interchangeComm (pos (ℕ.gcd (ℤ.abs x) (suc d-1)))
        (pos (ℕ.gcd (ℤ.abs y) (suc d-1'))) (↥ p) (↧ q)) ∙
        cong₂ (λ u w → u ℤ.· w)
         (sym (↥·gcd-lemma x d-1)) (sym (↧·gcd-lemma y d-1')))
       ((ℤ.·-interchangeComm' (pos (ℕ.gcd (ℤ.abs x) (suc d-1)))
        (pos (ℕ.gcd (ℤ.abs y) (suc d-1'))) (↥ q) (↧ p)) ∙
        cong₂ (λ u w → u ℤ.· w)
         (sym (↥·gcd-lemma y d-1')) (sym (↧·gcd-lemma x d-1)))
    step4 =
      sym (·₊₁-interchange (1+ predℕ (ℕ.gcd (ℤ.abs x) (suc d-1))) (↧₊₁ p)
       (1+ predℕ (ℕ.gcd (ℤ.abs y) (suc d-1'))) (↧₊₁ q)) ∙
      cong₂ (λ u v → u ·₊₁ v)
       (·₊₁-comm (1+ predℕ (ℕ.gcd (ℤ.abs x) (suc d-1))) (↧₊₁ p))
       (·₊₁-comm (1+ predℕ (ℕ.gcd (ℤ.abs y) (suc d-1'))) (↧₊₁ q)) ∙
      cong₂ (λ u v → u ·₊₁ v)
       (sym (↧₊₁·gcd-lemma x d-1)) (sym (↧₊₁·gcd-lemma y d-1'))

+overSameDenominator : ∀ x y d → [ x , d ] + [ y , d ] ≡ [ x ℤ.+ y , d ]
+overSameDenominator  x y d = (+ᵘ-def x y d d) ∙
  cong (λ u → [ u , d ·₊₁ d ]) (sym (ℤ.·DistL+ x y (ℕ₊₁→ℤ d))) ∙
  ·[]CancelR {x ℤ.+ y}{d} d

-- When normalised denominators are the same:
+overSameDenominator' : ∀{x}{y}{n} →
  n ≡ ↧₊₁ x → n ≡ ↧₊₁ y → x + y ≡ [ (↥ x) ℤ.+ (↥ y) , n ]
+overSameDenominator' {x}{y}{n} denx deny =
  sym step ∙ ·[]CancelR {(↥ x) ℤ.+ (↥ y)} {↧₊₁ x} c ∙
  cong (λ a → [ (↥ x) ℤ.+ (↥ y) , a ]) (sym denx)
  where
    c = ↧₊₁ y
    step : [ ((↥ x) ℤ.+ (↥ y)) ℤ.· (ℕ₊₁→ℤ c) , (↧₊₁ x) ·₊₁ c ] ≡ (x + y)
    step = cong
     (λ a -> [ a , (↧₊₁ x) ·₊₁ c ]) (ℤ.·DistL+ (↥ x) (↥ y) (ℕ₊₁→ℤ c)) ∙
      (cong (λ a → [ ((↥ x) ℤ.· (ℕ₊₁→ℤ c)) ℤ.+ ((↥ y) ℤ.· a) , (↧₊₁ x) ·₊₁ c ])
       (cong pos (sym (cong ℕ₊₁→ℕ ((sym denx) ∙ deny)))))

↧↧₊₁≡1 : ∀ n → [ ↧ n , ↧₊₁ n ] ≡ 1ℚ
↧↧₊₁≡1 n = ·[]Cancel {pos (suc zero)}{1+ zero}{↧ n}{↧₊₁ n}
  (↧₊₁ n) refl (sym (·₊₁-identityˡ (↧₊₁ n)))

--------------------------------------------------
-- Properties of _·_

·Comm : ∀ x y → x · y ≡ y · x
·Comm x y =
   cong₂ (λ u v → u · v) (≡↥↧₊₁ x) (≡↥↧₊₁ y) ∙ ·ᵘ-def (↥ x) (↥ y) (↧₊₁ x) (↧₊₁ y) ∙
   cong₂ (λ u v → [ u , v ]) (ℤ.·Comm (↥ x) (↥ y)) (·₊₁-comm (↧₊₁ x) (↧₊₁ y)) ∙
   sym (cong₂ (λ u v → u · v) (≡↥↧₊₁ y) (≡↥↧₊₁ x) ∙
    ·ᵘ-def (↥ y) (↥ x) (↧₊₁ y) (↧₊₁ x))

·Assoc : ∀ x y z → x · (y · z) ≡ (x · y) · z
·Assoc x y z =
  cong₃ (λ u v w → u · (v · w)) (≡↥↧₊₁ x) (≡↥↧₊₁ y) (≡↥↧₊₁ z) ∙
  cong (λ u → [ ↥ x , ↧₊₁ x ] · u) (·ᵘ-def (↥ y) (↥ z) (↧₊₁ y) (↧₊₁ z)) ∙
  ·ᵘ-def (↥ x) (↥ y ℤ.· ↥ z) (↧₊₁ x) (↧₊₁ y ·₊₁ ↧₊₁ z) ∙
  cong₂ (λ u v → [ u , v ]) (ℤ.·Assoc (↥ x) (↥ y) (↥ z))
   (·₊₁-assoc (↧₊₁ x) (↧₊₁ y) (↧₊₁ z)) ∙
  sym ( ·ᵘ-def (↥ x ℤ.· ↥ y) (↥ z) (↧₊₁ x ·₊₁ ↧₊₁ y) (↧₊₁ z)) ∙
  sym (cong (λ u → u · [ ↥ z , ↧₊₁ z ]) (·ᵘ-def (↥ x) (↥ y) (↧₊₁ x) (↧₊₁ y))) ∙
  sym (cong₃ (λ u v w → (u · v) · w) (≡↥↧₊₁ x) (≡↥↧₊₁ y) (≡↥↧₊₁ z))

·IdR : ∀ x → x · 1ℚ ≡ x
·IdR x = cong (λ u → u · 1ℚ) (≡↥↧₊₁ x) ∙ ·[]IdR  (↥ x) (↧₊₁ x) ∙ sym (≡↥↧₊₁ x)

·IdL : ∀ x → 1ℚ · x ≡ x
·IdL x = cong (λ u → 1ℚ · u ) (≡↥↧₊₁ x) ∙ ·[]IdL  (↥ x) (↧₊₁ x) ∙ sym (≡↥↧₊₁ x)

·ZeroR : ∀ x → x · 0ℚ ≡ 0ℚ
·ZeroR x = ↥≡0→≡0ℚ (cong ↥_ (cong₂ (λ u v → [ u , v ])
  (ℤ.·AnnihilR (↥ x)) refl))

isIntegralℚ : {p q : ℚ} → ¬ p ≡ 0ℚ → p · q ≡ 0ℚ → q ≡ 0ℚ
isIntegralℚ p@{(z , n) , c} q@{(z' , n') , c'} ¬p0 pq0 =
  ↥≡0→≡0ℚ (isIntegralℤ z z' zz0 nz0)
  where
    p' = sym [ c ]Def
    zz0 = [ℤ,-]≡0→ℤ≡0 (sym (cong₂ (λ u v → u · v) p' (sym [ c' ]Def) ∙
      (·ᵘ-def z z' (1+ n) (1+ n'))) ∙ pq0)
    nz0 = numerator[]≢0 z {1+ n} (subst (λ x → x)
      (cong (λ u → ¬ u ≡ 0ℚ) p') ¬p0)

·ZeroL : ∀ x → 0ℚ · x ≡ 0ℚ
·ZeroL x = ·Comm 0ℚ x ∙ ·ZeroR x

·-interchange : ∀ a b c d -> (a · b) · (c · d) ≡ (a · c) · (b · d)
·-interchange a b c d =
  sym (·Assoc a b (c · d)) ∙ cong (λ u → a · u) ((·Assoc b c d) ∙
  (cong (λ u → u · d) (·Comm b c)) ∙ sym (·Assoc c b d)) ∙ ·Assoc a c (b · d)

-------------------------------------------------------
 -- Properties of _+_ and _-_

+Comm : ∀ x y → x + y ≡ y + x
+Comm x y =
  cong₂ (λ a b → [ a , b ]) (ℤ.+Comm  ((↥ x) ℤ.· (↧ y)) ((↥ y) ℤ.· (↧ x)))
   (·₊₁-comm (↧₊₁ x) (↧₊₁ y))

+Assoc : ∀ x y z → x + (y + z) ≡ (x + y) + z
+Assoc x y z =
  cong₃ (λ u v w → u + (v + w)) (≡↥↧₊₁ x) (≡↥↧₊₁ y) (≡↥↧₊₁ z) ∙
  cong (λ u → [ ↥ x , ↧₊₁ x ] + u) (+ᵘ-def (↥ y) (↥ z) (↧₊₁ y ) (↧₊₁ z)) ∙
  +ᵘ-def (↥ x) yz (↧₊₁ x) dyz ∙
  cong₂ (λ u v → [ u , v ]) (lhs ∙ mid ∙ sym rhs)
   (·₊₁-assoc (↧₊₁ x) (↧₊₁ y) (↧₊₁ z)) ∙
  sym (+ᵘ-def xy (↥ z) dxy (↧₊₁ z)) ∙
  sym (cong (λ u → u + [ ↥ z , ↧₊₁ z ]) (+ᵘ-def (↥ x) (↥ y) (↧₊₁ x) (↧₊₁ y))) ∙
  sym (cong₃ (λ u v w → (u + v) + w) (≡↥↧₊₁ x) (≡↥↧₊₁ y) (≡↥↧₊₁ z))
  where
    xy = (↥ x ℤ.· ℕ₊₁→ℤ (↧₊₁ y)) ℤ.+ (↥ y ℤ.· ℕ₊₁→ℤ (↧₊₁ x))
    dxy = ↧₊₁ x ·₊₁ ↧₊₁ y
    yz = (↥ y ℤ.· ℕ₊₁→ℤ (↧₊₁ z)) ℤ.+ (↥ z ℤ.· ℕ₊₁→ℤ (↧₊₁ y))
    dyz = ↧₊₁ y ·₊₁ ↧₊₁ z
    lhs = cong₂ (λ u v → u ℤ.+ v)
     (cong (λ u → (↥ x) ℤ.· u) (·ℕ₊₁→ℤ-distr (↧₊₁ y) (↧₊₁ z)))
     (ℤ.·DistL+ (↥ y ℤ.· ℕ₊₁→ℤ (↧₊₁ z)) (↥ z ℤ.· ℕ₊₁→ℤ (↧₊₁ y)) (ℕ₊₁→ℤ (↧₊₁ x)))
    rhs = cong₂ (λ u v → u ℤ.+ v) (ℤ.·DistL+ (↥ x ℤ.· ℕ₊₁→ℤ (↧₊₁ y))
     (↥ y ℤ.· ℕ₊₁→ℤ (↧₊₁ x)) (ℕ₊₁→ℤ (↧₊₁ z)))
     (cong (λ u → (↥ z) ℤ.· u) (·ℕ₊₁→ℤ-distr (↧₊₁ x) (↧₊₁ y)))
    mid = ℤ.+Assoc ((↥ x) ℤ.· (ℕ₊₁→ℤ (↧₊₁ y) ℤ.· ℕ₊₁→ℤ (↧₊₁ z)))
     ((↥ y ℤ.· ℕ₊₁→ℤ (↧₊₁ z)) ℤ.· ℕ₊₁→ℤ (↧₊₁ x))
     ((↥ z ℤ.· ℕ₊₁→ℤ (↧₊₁ y)) ℤ.· ℕ₊₁→ℤ (↧₊₁ x)) ∙
     cong₃ (λ u v w → (u ℤ.+  v) ℤ.+  w)
     (ℤ.·Assoc (↥ x) (ℕ₊₁→ℤ (↧₊₁ y)) (ℕ₊₁→ℤ (↧₊₁ z)))
     (ℤ.·-rightComm (↥ y) (ℕ₊₁→ℤ (↧₊₁ z)) (ℕ₊₁→ℤ (↧₊₁ x)))
     ((sym (ℤ.·Assoc (↥ z) (ℕ₊₁→ℤ (↧₊₁ y)) (ℕ₊₁→ℤ (↧₊₁ x)))) ∙
     (cong (λ (u : ℤ) → (↥ z) ℤ.· u)
       (ℤ.·Comm (ℕ₊₁→ℤ (↧₊₁ y)) (ℕ₊₁→ℤ (↧₊₁ x)))))

+IdL : ∀ x → 0ℚ + x ≡ x
+IdL q@((z , n) , copr) =  cong₂ (λ a b → [ a , b ])
   (sym (ℤ.+Comm (z ℤ.· 1) 0) ∙ ℤ.·IdR z) (·₊₁-identityˡ (1+ n)) ∙
   [ copr ]Def

+IdR : ∀ x → x + 0ℚ ≡ x
+IdR x = +Comm x 0ℚ ∙ +IdL x

0-≡- : ∀ p → 0ℚ - p ≡ - p
0-≡- p@((z , n) , copr) = +IdL (- p)

+-comm-minus : ∀ x y → (- x) + y ≡ y - x
+-comm-minus x y = +Comm (- x) y

+InvR : ∀ x → x - x ≡ 0ℚ
+InvR x = +overSameDenominator' {x} {(- x)} {↧₊₁ x} refl (sym (↧₊₁-neg x)) ∙
  (cong (λ a → [ a , (↧₊₁ x) ]) (↥+↥-≡0 x)) ∙ ([0,-]≡0 (↧₊₁ x))

+InvL : ∀ x → (- x) + x ≡ 0ℚ
+InvL x = +-comm-minus x x ∙ +InvR x

+CancelL : ∀ x y z → x + y ≡ x + z → y ≡ z
+CancelL x y z p = sym (q y) ∙ cong ((- x) +_) p ∙ q z
  where q : ∀ y → (- x) + (x + y) ≡ y
        q y = +Assoc (- x) x y ∙ cong (_+ y) (+InvL x) ∙ +IdL y

+CancelR : ∀ x y z → x + y ≡ z + y → x ≡ z
+CancelR x y z p = +CancelL y x z (+Comm y x ∙ p ∙ +Comm z y)

-Invol : ∀ x → - (- x) ≡ x
-Invol x@((pos zero , n) , copr) = refl
-Invol x@((pos (suc m) , n) , copr) = refl
-Invol x@((negsuc m , n) , copr) = refl

subtractR : ∀ {x y z} → x + y ≡ z → x ≡ z - y
subtractR {x} {y} {z} xyz =  sym (+IdR x) ∙ cong (x +_) (sym (+InvR y)) ∙
  +Assoc x y (- y) ∙ cong (_- y) xyz

-nonZero : (p : ℚ) {{np : NonZero p}} → NonZero (- p)
-nonZero p@((pos (suc m) , n) , c) ⦃ np ⦄ = tt
-nonZero p@((negsuc m , n) , c) ⦃ np ⦄ = tt

-- Useful lemmas with _+_

+-interchange-assoc : ∀ a b c d → (a + b) + (c + d) ≡ a + (c + b + d)
+-interchange-assoc a b c d = sym (+Assoc a b (c + d)) ∙ cong (λ x → a + x)
 (+Assoc b c d ∙ cong (λ x → x + d) (+Comm b c))

+-interchange : ∀ a b c d → (a + b) + (c + d) ≡ (a + c) + (b + d)
+-interchange a b c d = step1 ∙ step3 ∙ sym step2
  where
    step1 : (a + b) + (c + d) ≡ a + (c + b + d)
    step1 = +-interchange-assoc a b c d
    step2 : (a + c) + (b + d) ≡ a + (b + c + d)
    step2 = +-interchange-assoc a c b d
    step3 : a + (c + b + d) ≡ a + (b + c + d)
    step3 = cong (λ x → a + (x + d)) (+Comm c b)

+-NonNegatives : ∀ {p}{q} → NonNegative p → NonNegative q → NonNegative (p + q)
+-NonNegatives p@{(pos m , d-1) , c} q@{(pos n , d-1') , c'} nnp nnq =
  subst (λ x → x) step2 tt
  where
    step1 : (↥ p) ℤ.· (↧ q) ℤ.+ (↥ q) ℤ.· (↧ p) ≡ pos (m ℕ.· suc d-1' ℕ.+ n ℕ.· suc d-1)
    step1 = (cong₂ (λ a b → a ℤ.+ b) (sym (ℤ.pos·pos m (suc d-1')))
      (sym (ℤ.pos·pos n (suc d-1)))) ∙ sym (ℤ.pos+ (m ℕ.· suc d-1') (n ℕ.· suc d-1))
    step2 = sym (cong (λ a → NonNegative [ a , (↧₊₁ p) ·₊₁ (↧₊₁ q) ]) step1)

-------------------------------------------------
-- Distributivity relations between _·_ and _+_

-≡-1· : ∀ x → (- x) ≡ -1ℚ · x
-≡-1· x@((pos zero , n) , c) = sym (·IdL ((pos zero , n) , c))
-≡-1· x@((pos (suc m) , n) , c) = sym (·IdL ((negsuc m , n) , c))
-≡-1· x@((negsuc m , n) , c) = sym (·IdL ((pos (suc m) , n) , c))

·DistR+ : ∀ x y z → x · (y + z) ≡ (x · y) + (x · z)
·DistR+ x y z =
  cong₃ (λ u v w → u · (v + w)) (≡↥↧₊₁ x) (≡↥↧₊₁ y) (≡↥↧₊₁ z) ∙
  cong (λ u → [ (↥ x) , (↧₊₁ x) ] · u) (+ᵘ-def (↥ y) (↥ z) (↧₊₁ y) (↧₊₁ z)) ∙
  ·ᵘ-def (↥ x) ((↥ y) ℤ.· ℕ₊₁→ℤ (↧₊₁ z) ℤ.+ (↥ z) ℤ.· ℕ₊₁→ℤ (↧₊₁ y))
   (↧₊₁ x) (↧₊₁ y ·₊₁ ↧₊₁ z) ∙
  cong₂ (λ u v → [ u , v ])
   (ℤ.·DistR+ (↥ x) ((↥ y) ℤ.· ℕ₊₁→ℤ (↧₊₁ z)) ((↥ z) ℤ.· ℕ₊₁→ℤ (↧₊₁ y)) ∙
    cong₂ (λ u v → u ℤ.+ v) (ℤ.·Assoc (↥ x) (↥ y) (ℕ₊₁→ℤ (↧₊₁ z)))
     (ℤ.·Assoc (↥ x) (↥ z) (ℕ₊₁→ℤ (↧₊₁ y))))
   (·₊₁-assoc (↧₊₁ x) (↧₊₁ y) (↧₊₁ z))  ∙
  sym (·[]CancelR
   {(↥ x ℤ.· ↥ y) ℤ.· ℕ₊₁→ℤ (↧₊₁ z) ℤ.+ (↥ x ℤ.· ↥ z) ℤ.· ℕ₊₁→ℤ (↧₊₁ y)}
   {(↧₊₁ x) ·₊₁ (↧₊₁ y) ·₊₁ (↧₊₁ z)} (↧₊₁ x)) ∙
  sym ( cong₃ (λ u v w → [ u ℤ.+ v , w ])
   (cong (λ u →  (↥ x ℤ.· ↥ y) ℤ.· u) (·ℕ₊₁→ℤ-distr (↧₊₁ x) (↧₊₁ z) ∙
    ℤ.·Comm (ℕ₊₁→ℤ (↧₊₁ x)) (ℕ₊₁→ℤ (↧₊₁ z))) ∙ (ℤ.·Assoc ((↥ x) ℤ.· (↥ y))
     (ℕ₊₁→ℤ (↧₊₁ z)) (ℕ₊₁→ℤ (↧₊₁ x))))
   (cong (λ u →  (↥ x ℤ.· ↥ z) ℤ.· u) (·ℕ₊₁→ℤ-distr (↧₊₁ x) (↧₊₁ y) ∙
    ℤ.·Comm (ℕ₊₁→ℤ (↧₊₁ x)) (ℕ₊₁→ℤ (↧₊₁ y))) ∙
    ℤ.·Assoc (↥ x ℤ.· ↥ z) (ℕ₊₁→ℤ (↧₊₁ y)) (ℕ₊₁→ℤ (↧₊₁ x)))
   (cong (λ u → (↧₊₁ x ·₊₁ ↧₊₁ y) ·₊₁ u) (·₊₁-comm (↧₊₁ x) (↧₊₁ z)) ∙
    ·₊₁-assoc (↧₊₁ x ·₊₁ ↧₊₁ y) (↧₊₁ z) (↧₊₁ x)) ∙
   cong (λ u → [ u , (↧₊₁ x) ·₊₁ (↧₊₁ y) ·₊₁ (↧₊₁ z) ·₊₁ (↧₊₁ x) ])
    (sym (ℤ.·DistL+ (((↥ x) ℤ.· (↥ y)) ℤ.· ℕ₊₁→ℤ (↧₊₁ z))
     ((↥ x ℤ.· ↥ z) ℤ.· ℕ₊₁→ℤ (↧₊₁ y)) (ℕ₊₁→ℤ (↧₊₁ x))))) ∙
  sym (cong₂ (λ u v → u + v) (·ᵘ-def (↥ x) (↥ y) (↧₊₁ x) (↧₊₁ y))
   (·ᵘ-def (↥ x) (↥ z) (↧₊₁ x) (↧₊₁ z)) ∙
   +ᵘ-def (↥ x ℤ.· ↥ y) (↥ x ℤ.· ↥ z) (↧₊₁ x ·₊₁ ↧₊₁ y) (↧₊₁ x ·₊₁ ↧₊₁ z)) ∙
  sym (cong₃ (λ u v w → (u · v) + (u · w)) (≡↥↧₊₁ x) (≡↥↧₊₁ y) (≡↥↧₊₁ z))

·DistL+ : ∀ x y z → (x + y) · z ≡ (x · z) + (y · z)
·DistL+ x y z =
  ·Comm (x + y) z ∙ ·DistR+ z x y ∙ cong₂ (λ u v → u + v) (·Comm z x) (·Comm z y)

-[]distr : ∀ x → - x ≡ [ ℤ.- (↥ x) , ↧₊₁ x  ]
-[]distr x = ≡↥↧₊₁ (- x) ∙ cong₂ (λ u v → [ u ,  v ]) (↥-neg x) (↧₊₁-neg x)

-DistrL· : ∀ x y → - (x · y) ≡ (- x) · y
-DistrL· x y =
  -≡-1· (x · y) ∙ ·Assoc -1ℚ x y ∙ cong (λ u → u · y) (sym (-≡-1· x))

-DistrR· : ∀ x y → - (x · y) ≡ x · (- y)
-DistrR· x y = cong -_ (·Comm x y) ∙ -DistrL· y x ∙ ·Comm (- y) x

-[]distr' : ∀ a b → - [ a , b ] ≡ [ ℤ.- a , b ]
-[]distr' (pos zero) b =  refl
-[]distr' (pos (suc n)) b = refl
-[]distr' (negsuc n) b = -Invol (normalise (suc n) b)

-dist+ : ∀ p q → - (p + q) ≡ (- p) + (- q)
-dist+ p q = -[]distr' p+q-num p+q-den ∙ cong₂ (λ a b → [ a , b ]) ths bhs
  where
    p+q-num = (↥ p) ℤ.· (↧ q) ℤ.+ (↥ q) ℤ.· (↧ p)
    -p-q-num = (↥ (- p)) ℤ.· (↧ (- q)) ℤ.+ (↥ (- q)) ℤ.· (↧ (- p))
    p+q-den = (↧₊₁ p) ·₊₁ (↧₊₁ q)
    -p-q-den = (↧₊₁ (- p)) ·₊₁ (↧₊₁ (- q))
    lhs : ↥ (- p) ℤ.· ↧ (- q) ≡ ℤ.- (↥ p ℤ.· ↧ q)
    lhs = cong₂ (λ a b → a ℤ.· b) (↥-neg p) (↧-neg q) ∙
      sym (ℤ.-DistL· (↥ p) (↧ q))
    rhs : ↥ (- q) ℤ.· ↧ (- p) ≡ ℤ.- (↥ q ℤ.· ↧ p)
    rhs = cong₂ (λ a b → a ℤ.· b) (↥-neg q) (↧-neg p) ∙
      sym (ℤ.-DistL· (↥ q) (↧ p))
    ths : ℤ.- p+q-num ≡ -p-q-num
    ths = ℤ.-Dist+ ((↥ p) ℤ.· (↧ q)) ((↥ q) ℤ.· (↧ p)) ∙
      sym (cong₂ (λ a b → a ℤ.+ b) lhs rhs)
    bhs : p+q-den ≡ -p-q-den
    bhs = sym (cong₂ (λ a b → a ·₊₁ b) (↧₊₁-neg p) (↧₊₁-neg q))

-dist- : ∀ p q → - (p - q) ≡ q - p
-dist- p q = -dist+ p (- q) ∙ cong ((- p) +_) (-Invol q) ∙ +Comm (- p) q

-·-≡· : ∀ x y → (- x) · (- y) ≡ x · y
-·-≡· x y = sym ((cong -_ (·Comm (- y) x)) ∙ (-DistrL· x (- y))) ∙
  -DistrL· (- y) x ∙ ·Comm (- (- y)) x ∙ cong (λ u → x · u) (-Invol y)

·-≡-· : ∀ x y → x · (- y) ≡ (- x) · y
·-≡-· x y = sym (-DistrR· x y) ∙ -DistrL· x y

·-NonZero : (p q : ℚ) {{np : NonZero p}}{{nq : NonZero q}} → NonZero (p · q)
·-NonZero p q {{np}}{{nq}} =
  ≢0→NonZero (converse (isIntegralℚ {p}{q} (NonZero→≢0 np)) (NonZero→≢0 nq))

·-NonNegatives : ∀ {p}{q} → NonNegative p → NonNegative q → NonNegative (p · q)
·-NonNegatives {p@((pos m , d-1) , c)} {q@((pos n , d-1') , c')} tt tt = nnpq
  where
    step = cong (λ a → NonNegative [ a , (↧₊₁ p) ·₊₁ (↧₊₁ q) ]) (ℤ.pos·pos m n)
    nnpq : NonNegative (p · q)
    nnpq = subst (λ x → x) step tt

-------------------------------------------------------
-- Some helper functions for properties of 1/_ and _/_

substNonZero : {p q : ℚ} → {{nz : NonZero p}} → p ≡ q → NonZero q
substNonZero {p}{q}{{nz}} pq = subst NonZero pq nz

instance
  nonZero-1/' : {q : ℚ} → {{nz : NonZero q}} → NonZero (1/ q)
  nonZero-1/' {(pos (suc m) , n) , c} ⦃ nz ⦄ = tt
  nonZero-1/' {(negsuc m , n) , c} ⦃ nz ⦄ = tt

nonZero-1/ : (q : ℚ) {{nz : NonZero q}} → NonZero (1ℚ / q)
nonZero-1/ q =
  subst (λ z → z) (cong NonZero (sym (·IdL (1/ q)))) (nonZero-1/' {q})

pos/-nonZero : (p q : ℚ) → {{nz : NonZero p}}{{nz' : NonZero q}} → NonZero (p / q)
pos/-nonZero p q {{nz}}{{nz'}} = subst (λ z → z)
  (cong NonZero ((·Assoc p 1ℚ (1/ q)) ∙ cong (λ u → u · 1/ q) (·IdR p)))
  (·-NonZero p (1ℚ · 1/ q) {{nz}}{{step}})
  where
    step = subst (λ z → z) (cong NonZero (sym (·IdL (1/ q)))) (nonZero-1/' {q})

private
  -- Absolute value of a non-zero numerator of a ℚ as an ℕ₊₁
  abs↥₊₁ : (p : ℚ) → {{nz : NonZero p}} → ℕ₊₁
  abs↥₊₁ p@((pos (suc m) , n) , c) = 1+ m
  abs↥₊₁ p@((negsuc m , n) , c) = 1+ m

  abs↥₊₁-def : (p : ℚ) → {{nz : NonZero p}} →
    ℕ₊₁→ℕ (abs↥₊₁ p {{nz}}) ≡ ℤ.abs (↥ p)
  abs↥₊₁-def p@((pos (suc m) , n) , c) ⦃ nz ⦄ = refl
  abs↥₊₁-def p@((negsuc m , n) , c) ⦃ nz ⦄ = refl

  abs↥₊₁-cong : ∀ p q {{nz : NonZero p}}{{nz' : NonZero q}} →
    p ≡ q → abs↥₊₁ p ≡ abs↥₊₁ q
  abs↥₊₁-cong p@((pos (suc m) , n) , c) q@((pos (suc m') , n') , c')
    ⦃ nz ⦄ ⦃ nz' ⦄ pq =
      cong 1+_ (injSuc (ℤ.injPos (cong (λ u → fst (fst u)) pq)))
  abs↥₊₁-cong p@((pos (suc m) , n) , c) q@((negsuc m' , n') , c')
    ⦃ nz ⦄ ⦃ nz' ⦄ pq = ⊥.elim {ℓ-zero}{λ x → 1+ m ≡ 1+ m'}
    (ℤ.posNotnegsuc (suc m) m' (cong (λ u → fst (fst u)) pq))
  abs↥₊₁-cong p@((negsuc m , n) , c) q@((pos (suc m') , n') , c')
    ⦃ nz ⦄ ⦃ nz' ⦄ pq = ⊥.elim {ℓ-zero}{λ x → 1+ m ≡ 1+ m'}
    (ℤ.negsucNotpos m (suc m') (cong (λ u → fst (fst u)) pq))
  abs↥₊₁-cong p@((negsuc m , n) , c) q@((negsuc m' , n') , c')
    ⦃ nz ⦄ ⦃ nz' ⦄ pq = cong 1+_ (ℤ.injNegsuc (cong (λ u → fst (fst u)) pq))

-------------------------------------------------
-- Properties of 1/_ and _/_

1ℚ/≡1/ : (q : ℚ) → {{nz : NonZero q}} → 1ℚ / q ≡ 1/ q
1ℚ/≡1/ q {{nz}} = ·IdL (1/ q)

1/-as-[] : (q : ℚ) → {{nz : NonZero q}} →
  (1/ q) {{nz}} ≡ [ (ℤ.sign (↥ q)) ℤ.· ℕ₊₁→ℤ (↧₊₁ q) , (abs↥₊₁ q) {{nz}} ]
1/-as-[] ((pos (suc m) , n) , c) ⦃ nz ⦄ = sym (normalise-coprime (symGCD c))
1/-as-[] ((negsuc m , n) , c) ⦃ nz ⦄ = sym (cong -_ (normalise-coprime (symGCD c)))

1/-subst : {a b : ℚ} → (ab : a ≡ b) {{nz : NonZero a}}{{nz' : NonZero b}} →
  (1/ a) {{nz}} ≡ (1/ b) {{nz'}}
1/-subst {a}{b} ab {{nz}} {{nz'}} = 1/-as-[] a {{nz}} ∙ cong₂ (λ u v → [ u , v ])
  (cong (λ u → ℤ.sign (↥ u) ℤ.· ℕ₊₁→ℤ (↧₊₁ u)) ab)
   (abs↥₊₁-cong a b {{nz}}{{nz'}} ab) ∙ sym (1/-as-[] b {{nz'}})

1/-subst* : {a b : ℚ} → (ab : a ≡ b) → {{nz : NonZero a}} →
  1/ a ≡ (1/ b) {{substNonZero {{nz}} ab}}
1/-subst* {a}{b} ab {{nz}} = let nz' = substNonZero {{nz}} ab in 1/-as-[] a {{nz}} ∙
  cong₂ (λ u v → [ u , v ])
   (cong (λ u → ℤ.sign (↥ u) ℤ.· ℕ₊₁→ℤ (↧₊₁ u)) ab)
    (abs↥₊₁-cong a b {{nz}}{{nz'}} ab) ∙
  sym (1/-as-[] b {{nz'}})

/-invol' : (q : ℚ) {{nz : NonZero q}}{{nz' : NonZero (1/ q)}} →
  (1/ (1/ q) {{nz}}) {{nz'}} ≡ q
/-invol' ((pos (suc m) , n) , c) ⦃ nz ⦄ {{nz'}} = refl
/-invol' ((negsuc m , n) , c) ⦃ nz ⦄ {{nz'}} = refl

/-invol : (q : ℚ) {{nz : NonZero q}}{{nz' : NonZero (1ℚ / q)}} →
  (1ℚ / (1ℚ / q)) ≡ q
/-invol q {{nz}}{{nz'}} = 1ℚ/≡1/ (1ℚ / q) {{nz'}} ∙
  (1/-subst (1ℚ/≡1/ q {{nz}})
  {{nz'}}{{nonZero-1/'}}) ∙ /-invol' q

-- specialises one of the instances of /-invol for convenience
/-invol* : (q : ℚ) {{nz : NonZero q}} →
  (1ℚ / (1ℚ / q)) {{nonZero-1/ q}} ≡ q
/-invol* q {{nz}} = /-invol q {{nz}} {{nonZero-1/ q}}

1/normalise-def : ∀ m n {{nz : NonZero (normalise (suc m) (1+ n))}} →
  (1/ normalise (suc m) (1+ n)) {{nz}} ≡ normalise (suc n) (1+ m)
1/normalise-def m n {{nz}} = 1/-subst p≡p' {{nz}}{{tt}} ∙ ↥↧₋₁-injective step
  where
    sm' = fst (toCoprime (suc m , (1+ n)))
    m' = predℕ sm'
    sm'≡sucm' = suc-predℕ sm' (coprime≢0 m (1+ n))
    n' = snd (toCoprime (suc m , (1+ n)))
    c' = toCoprimeAreCoprime (suc m , (1+ n))
    p≡p' : ((pos sm' , -1+ n') , c') ≡ ((pos (suc m') , -1+ n') ,
           ( subst (λ u → areCoprime (u , ℕ₊₁→ℕ n')) sm'≡sucm' c'))
    p≡p' = ℚ-unique₊₁ (cong pos sm'≡sucm') refl
    step : (pos (ℕ₊₁→ℕ n') , m') ≡ (pos (fst (toCoprime (suc n , (1+ m)))) ,
      -1+ (snd (toCoprime (suc n , (1+ m)))))
    step i = ((cong pos (sym (symCoprime n m))) i) ,
      (cong predℕ (sym sm'≡sucm' ∙ (symCoprime m n))) i

1/possuc-def : ∀ m n c →
  (1/ ((pos (suc m) , n) , c)) {{tt}} ≡ ((pos (suc n) , m) , symGCD c)
1/possuc-def m n c = refl

1/negsuc-def : ∀ m n c →
  (1/ ((negsuc m , n) , c)) {{tt}} ≡ ((negsuc n , m) , symGCD c)
1/negsuc-def m n c = refl

1/-≡-1/ : (p : ℚ) {{np : NonZero p}}{{np' : NonZero (- p)}} →
  1/ (- p) ≡ - (1/ p)
1/-≡-1/ p@((pos (suc m) , n) , c) = refl
1/-≡-1/ p@((negsuc m , n) , c) = refl

-- specialises NonZero (- p) instance
1/-p≡-1/p* : (p : ℚ) {{np : NonZero p}} →
  (1/ (- p)) {{ -nonZero p}} ≡ - ((1/ p) {{np}})
1/-p≡-1/p* p {{np}} = 1/-≡-1/ p {{np}}{{ -nonZero p}}

/distL+ : ∀ p q r {{nr : NonZero r}} → (p + q) / r ≡ (p / r) + (q / r)
/distL+ p q r {{nr}} = ·DistL+ p q (1/ r)


module 1/-helpers where

  1/possuc·possuc : ∀ {m}{m'}{n}{n'} c c'
    {{npq : NonZero ((((pos (suc m) , n) , c)) · (((pos (suc m') , n') , c')))}} →
    (1/ ((((pos (suc m) , n) , c)) · (((pos (suc m') , n') , c')))) {{npq}} ≡
     (1/ ((pos (suc m) , n) , c)) {{tt}} · (1/ ((pos (suc m') , n') , c')) {{tt}}
  1/possuc·possuc {m}{m'}{n}{n'} c c' {{npq}} = 1/-subst* step {{npq}} ∙
    1/normalise-def (m' ℕ.+ m ℕ.· suc m') (n' ℕ.+ n ℕ.· suc n') {{substNonZero step}} ∙
    sym (cong (λ u → [ u , 1+ (m' ℕ.+ m ℕ.· suc m') ])
     (sym (ℤ.pos·pos (suc n) (suc n')))) ∙
    sym (·ᵘ-def (pos (suc n)) (pos (suc n')) (1+ m) (1+ m')) ∙
    cong₂ (λ u v → u · v)  ([_]Def {pos (suc n)}{m} (symGCD c))
     ([_]Def {pos (suc n')}{m'} (symGCD c'))
    where
      step = cong₂ (λ u v → u · v) (sym ([_]Def {pos (suc m)} {n} c))
         (sym ([_]Def {pos (suc m')}{n'} c')) ∙
        ·ᵘ-def (pos (suc m)) (pos (suc m')) (1+ n) (1+ n') ∙
        cong (λ u → [ u , (1+ n) ·₊₁ (1+ n') ])
         (sym (ℤ.pos·pos (suc m) (suc m')))

  1/possuc·negsuc : ∀ {m}{m'}{n}{n'} c c'
    {{npq : NonZero ((((pos (suc m) , n) , c)) · (((negsuc m' , n') , c')))}} →
    (1/ ((((pos (suc m) , n) , c)) · (((negsuc m' , n') , c')))) {{npq}} ≡
     (1/ ((pos (suc m) , n) , c)) {{tt}} · (1/ ((negsuc m' , n') , c')) {{tt}}
  1/possuc·negsuc {m}{m'}{n}{n'} c c' {{npq}} = (sym (1/-subst -pp'≡ {{nnpp'}}{{npq}})) ∙
    1/-≡-1/ pp' {{npp'}}{{nnpp'}} ∙
    (cong -_ (1/possuc·possuc {m}{m'}{n}{n'} c c' {{npp'}})) ∙
    -DistrR· ((1/ p) {{tt}}) ((1/ p') {{tt}}) ∙
    (cong (λ u → ((1/ p) {{tt}}) · u) (sym (1/-≡-1/ p' {{tt}}{{tt}})))
    where
      p : ℚ ; p' : ℚ ; pp' = p · p' ; -p' : ℚ
      p = ((pos (suc m) , n) , c) ; p' = ((pos (suc m') , n') , c')
      -p' = ((negsuc m' , n') , c')
      -pp'≡ : - pp' ≡ p · -p'
      -pp'≡ = -DistrR· p p'
      nnpp' : NonZero (- (p · p'))
      nnpp' = subst (λ x → x) (cong NonZero (sym -pp'≡)) npq
      npp' = ·-NonZero p p' {{tt}}{{tt}}

  1/negsuc·possuc : ∀ {m}{m'}{n}{n'} c c'
    {{np'p : NonZero ((((negsuc m , n) , c)) · (((pos (suc m') , n') , c')))}} →
    (1/ ((((negsuc m) , n) , c) · ((pos (suc m') , n') , c'))) {{np'p}} ≡
     (1/ ((negsuc m , n) , c)) {{tt}} · (1/ ((pos (suc m') , n') , c')) {{tt}}
  1/negsuc·possuc {m}{m'}{n}{n'} c c' {{np'p}} =
    1/-subst (·Comm -p p') {{np'p}}{{np'np}} ∙
    1/possuc·negsuc {m'}{m}{n'}{n} c' c {{np'np}} ∙
    ·Comm ((1/ p') {{tt}}) ((1/ -p) {{tt}})
    where
      p : ℚ ; p' : ℚ ; -p : ℚ ; -p' : ℚ
      p' = ((pos (suc m') , n') , c') ; -p' = ((negsuc m' , n') , c')
      p = ((pos (suc m) , n) , c) ; -p = ((negsuc m , n) , c)
      np'np = ·-NonZero p' -p {{tt}}{{tt}}

  1/negsuc·negsuc : ∀ {m}{m'}{n}{n'} c c'
    {{npq : NonZero (((negsuc m , n) , c) · ((negsuc m' , n') , c'))}} →
    (1/ ((((negsuc m) , n) , c) · ((negsuc m' , n') , c'))) {{npq}} ≡
     (1/ ((negsuc m , n) , c)) {{tt}} · (1/ (((negsuc m') , n') , c')) {{tt}}
  1/negsuc·negsuc {m}{m'}{n}{n'} c c' {{npq}} =
    1/-subst (-·-≡· p p') {{npq}} {{npp'}} ∙
    1/possuc·possuc {m}{m'}{n}{n'} c c' {{npp'}} ∙
    sym (-·-≡· ((1/ p) {{tt}}) ((1/ p') {{tt}})) ∙
    cong₂ (λ u v → u · v) (sym (1/-≡-1/ p {{tt}}{{tt}}))
     (sym (1/-≡-1/ p' {{tt}}{{tt}}))
    where
      p : ℚ ; -p : ℚ ; p' : ℚ ; -p' : ℚ
      p = ((pos (suc m) , n) , c) ; -p = (((negsuc m) , n) , c)
      p' = ((pos (suc m') , n') , c') ; -p' = (((negsuc m') , n') , c')
      npp' = ·-NonZero p p' {{tt}}{{tt}}

open 1/-helpers

·1/≡/ : (p q : ℚ) → {{nz : NonZero q}} → p · (1ℚ / q) ≡ p / q
·1/≡/ p q ⦃ nz ⦄ = cong (λ u → p · u) (1ℚ/≡1/ q)

·/Assoc : (p q r : ℚ) → {{nz : NonZero r}} → p · (q / r) ≡ (p · q) / r
·/Assoc p q r ⦃ nz ⦄ = cong (λ u → p · (q · u)) (sym (1ℚ/≡1/ r)) ∙
  ·Assoc p q (1ℚ / r) ∙ ·1/≡/ (p · q) r

0/≡0 : (q : ℚ) {{nz : NonZero q}} → 0ℚ / q ≡ 0ℚ
0/≡0 q {{nz}} = sym (·1/≡/ 0ℚ q) ∙ (·ZeroL (1ℚ / q))

/-self : (p : ℚ) → {{nz : NonZero p}} → p / p ≡ 1ℚ
/-self p@((pos (suc n) , d-1) , c) ⦃ nz ⦄ =
  sym (·[]CancelL {(pos (suc n) ℤ.· ℕ₊₁→ℤ (1+ d-1))} (1+ zero)) ∙
  ·[]Cancel {pos (suc zero)}{1+ zero}{pos (suc n) ℤ.· ℕ₊₁→ℤ (1+ d-1)}
   {(1+ zero) ·₊₁ ((1+ d-1) ·₊₁ (1+ n))} ((1+ d-1) ·₊₁ (1+ n))
   (ℤ.·Comm (ℕ₊₁→ℤ (1+ n)) (ℕ₊₁→ℤ (1+ d-1)) ∙
  sym (·ℕ₊₁→ℤ-distr (1+ d-1) (1+ n))) refl
/-self p@((negsuc n , d-1) , c) ⦃ nz ⦄ =
  -·-≡· ((pos (suc n) , d-1) , c) (((pos (suc d-1)) , n) , symGCD c) ∙
  /-self ((pos (suc n) , d-1) , c) {{tt}}

·-inv : (p q : ℚ) →
  {{np : NonZero p}}{{nq : NonZero q}}{{npq : NonZero (p · q)}} →
  (1/ (p · q)) ≡ (1/ p) · (1/ q)
·-inv p@((pos (suc m) , n) , c) q@((pos (suc m') , n') , c')
  ⦃ np ⦄ ⦃ nq ⦄ ⦃ npq ⦄ = 1/possuc·possuc c c' {{npq}}
·-inv p@((pos (suc m) , n) , c) q@((negsuc m' , n') , c')
  ⦃ np ⦄ ⦃ nq ⦄ ⦃ npq ⦄ = 1/possuc·negsuc c c' {{npq}}
·-inv p@((negsuc m , n) , c) q@((pos (suc m') , n') , c')
  ⦃ np ⦄ ⦃ nq ⦄ ⦃ npq ⦄ = 1/negsuc·possuc c c' {{npq}}
·-inv p@((negsuc m , n) , c) q@((negsuc m' , n') , c')
  ⦃ np ⦄ ⦃ nq ⦄ ⦃ npq ⦄ = 1/negsuc·negsuc c c' {{npq}}

·-inv* : (p q : ℚ) →
  {{np : NonZero p}}{{nq : NonZero q}} →
  (1/ (p · q)) {{·-NonZero p q}} ≡ (1/ p) · (1/ q)
·-inv* p q {{np}}{{nq}} = ·-inv p q {{np}}{{nq}}{{·-NonZero p q}}

/-cancelˡ : (p q : ℚ) → {{np : NonZero p}}{{nq : NonZero q}}
  {{npq : NonZero (p · q)}} → (p / (p · q)) {{npq}} ≡ 1ℚ / q
/-cancelˡ p q {{np}}{{nq}}{{npq}} =
  cong (λ u → p · u) (·-inv p q {{np}}{{nq}}{{npq}}) ∙
  ·Assoc p (1/ p) (1/ q) ∙ cong (λ u → u · 1/ q) (/-self p)

/-cancelˡ* : (p q : ℚ) → {{np : NonZero p}}{{nq : NonZero q}}
  → (p / (p · q)) {{·-NonZero p q}} ≡ 1ℚ / q
/-cancelˡ* p q {{np}}{{nq}} = /-cancelˡ p q {{np}}{{nq}}{{·-NonZero p q}}

·/-split : (p q r s : ℚ) →
  {{nr : NonZero r}} {{ns : NonZero s}}{{nrs : NonZero (r · s)}} →
  (p · q) / (r · s) ≡ (p / r) · (q / s)
·/-split p q r s ⦃ nr ⦄ ⦃ ns ⦄ ⦃ nqr ⦄ =
  cong (λ u → (p · q) · u) (·-inv r s) ∙ ·-interchange p q (1/ r) (1/ s)

·/-split* : (p q r s : ℚ) →
  {{nr : NonZero r}} {{ns : NonZero s}} →
  ((p · q) / (r · s)) {{·-NonZero r s}} ≡ (p / r) · (q / s)
·/-split* p q r s ⦃ nr ⦄ ⦃ ns ⦄ =
  ·/-split p q r s {{nr}}{{ns}}{{·-NonZero r s}}

·/CancelL : (p q r : ℚ) {{np : NonZero p}}{{nr : NonZero r}}
  {{npr : NonZero (p · r)}} → (p · q) / (p · r) ≡ q / r
·/CancelL p q r {{np}}{{nr}}{{npr}} = ·/-split p q p r {{np}}{{nr}}{{npr}} ∙
  cong (λ u → u · (q / r)) (/-self p) ∙ ·IdL (q / r)

·/CancelLR : (p q r : ℚ) {{np : NonZero p}}{{nr : NonZero r}}
  {{npr : NonZero (r · p)}} → (p · q) / (r · p) ≡ q / r
·/CancelLR p q r {{np}}{{nr}}{{nrp}} = let npr = ·-NonZero p r in sym
   (cong (λ u → (p · q) · u) (1/-subst (·Comm p r) {{npr}}{{nrp}})) ∙
  ·/CancelL p q r {{np}}{{nr}}{{npr}}

·/CancelRL : (p q r : ℚ) {{np : NonZero p}}{{nr : NonZero r}}
  {{npr : NonZero (p · r)}} → (q · p) / (p · r) ≡ q / r
·/CancelRL p q r {{np}}{{nr}}{{npr}} =
  (cong (λ u → u / (p · r)) (·Comm q p)) ∙
  ·/CancelL p q r {{np}}{{nr}}{{npr}}

·/CancelR : (p q r : ℚ) {{np : NonZero p}}{{nr : NonZero r}}
  {{npr : NonZero (r · p)}} → (q · p) / (r · p) ≡ q / r
·/CancelR p q r {{np}}{{nr}}{{nrp}} = cong (λ u → u / (r · p)) (·Comm q p) ∙
  ·/CancelLR p q r {{np}}{{nr}}{{nrp}}

·/CancelL* : (p q r : ℚ) {{np : NonZero p}}{{nr : NonZero r}} →
  ((p · q) / (p · r)) {{·-NonZero p r}} ≡ q / r
·/CancelL* p q r {{np}}{{nr}} = ·/CancelL p q r {{np}}{{nr}}{{·-NonZero p r}}

·/CancelLR* : (p q r : ℚ) {{np : NonZero p}}{{nr : NonZero r}} →
  ((p · q) / (r · p)) {{·-NonZero r p}} ≡ q / r
·/CancelLR* p q r {{np}}{{nr}} = ·/CancelLR p q r {{np}} {{nr}} {{·-NonZero r p}}

·/CancelRL* : (p q r : ℚ) {{np : NonZero p}}{{nr : NonZero r}} →
  ((q · p) / (p · r)) {{·-NonZero p r}} ≡ q / r
·/CancelRL* p q r {{np}}{{nr}} = ·/CancelRL p q r {{np}}{{nr}}{{·-NonZero p r}}

·/CancelR* : (p q r : ℚ) {{np : NonZero p}}{{nr : NonZero r}}  →
  ((q · p) / (r · p)) {{·-NonZero r p}} ≡ q / r
·/CancelR* p q r {{np}}{{nr}} = ·/CancelR p q r {{np}}{{nr}}{{·-NonZero r p}}

1/-flip : (p q : ℚ) {{np : NonZero p}}{{nq : NonZero q}}
  {{npq : NonZero (p / q)}} → 1ℚ / (p / q) ≡ q / p
1/-flip p q {{np}}{{nq}}{{npq}} =
  (cong (λ u → u / (p / q)) (sym (/-self q))) ∙ (cong (λ u → (q · 1/ q) · u)
   (1/-subst {p / q} {p / q} refl {{npq}}{{·-NonZero p (1/ q)}})) ∙
  ·/CancelR* (1/ q) q p {{nonZero-1/' {q}}}{{np}}

1/-flip* : (p q : ℚ) {{np : NonZero p}}{{nq : NonZero q}} →
  (1ℚ / (p / q)) {{pos/-nonZero p q}} ≡ q / p
1/-flip* p q {{np}}{{nq}} = 1/-flip p q {{np}}{{nq}}{{pos/-nonZero p q}}

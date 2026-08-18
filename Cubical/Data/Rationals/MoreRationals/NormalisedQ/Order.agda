module Cubical.Data.Rationals.MoreRationals.NormalisedQ.Order where

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat as ℕ using (ℕ; suc; zero)
open import Cubical.Foundations.Prelude
open import Cubical.Relation.Nullary
open import Cubical.Data.Sigma
open import Cubical.Data.Int.Order as ℤ using ()
open import Cubical.Data.Int as ℤ
  using (ℤ; pos; negsuc; isIntegralℤ; injPos; pos·pos; pos+)
open import Cubical.Data.NatPlusOne as ℕ₊₁
  using (1+_; _·₊₁_; ℕ₊₁; ℕ₊₁→ℕ; ℕ₊₁→ℕ-inj; ·₊₁-comm; -1+_;
    ·₊₁-identityʳ; ·₊₁-identityˡ ; ·₊₁-assoc)
open import Cubical.Data.Rationals.MoreRationals.NormalisedQ

private
  variable
    ℓ ℓ' : Level
    m n o : ℚ

-- Helper functions
private
  isProp× : ∀ (A : Type ℓ) (B : Type ℓ') → isProp A → isProp B → isProp (A × B)
  isProp× A B ispA ispB (a₁ , b₁) (a₂ , b₂) =
    cong₂ (λ a b → a , b) (ispA a₁ a₂) (ispB b₁ b₂)

  ℤweaken≡→≤ : ∀ {m}{n} → m ≡ n → m ℤ.≤ n
  ℤweaken≡→≤ {m}{n} mn =
    subst (λ x → x) (cong (λ x → x ℤ.≤ n) (sym mn)) (ℤ.isRefl≤ {n})

  ℤ¬≤→¬≡ : ∀ {m n : ℤ} → ¬ m ℤ.≤ n → ¬ m ≡ n
  ℤ¬≤→¬≡ {m}{n} ¬mn = λ x → ¬mn (ℤweaken≡→≤ x)

  ℤ<→¬≡ : ∀ {m n : ℤ} → m ℤ.< n → ¬ m ≡ n
  ℤ<→¬≡ {m}{n} m<n m≡n =
    ⊥.elim (ℤ.isAsym< {m}{n} m<n (subst (λ u → u ℤ.≤ m) m≡n (ℤ.isRefl≤ {m})))

infix 4 _<_ _≥_ _>_ _⋖_

_<_ : ℚ → ℚ → Type
m < n = (↥ m ℤ.· ↧ n) ℤ.< (↥ n ℤ.· ↧ m)

_⋖_ : ℚ → ℚ → Type
m ⋖ n = (m ≤ n) × (¬ m ≃ n)

_≥_ : ℚ → ℚ → Type
m ≥ n = n ≤ m

_>_ : ℚ → ℚ → Type
m > n = n < m

<→¬≃ : m < n → ¬ m ≃ n
<→¬≃ {m}{n} m<n = ¬*≡* (ℤ<→¬≡ m<n)

isIrrefl< : ¬ m < m
isIrrefl< = ℤ.isIrrefl<

<-weaken : m < n → m ≤ n
<-weaken m<n = ℤ.<-weaken m<n

weaken≡→≤ : m ≡ n → m ≤ n
weaken≡→≤ mn = zero , *≡*⁻¹ (≡→≃ mn)

<→¬≡ : m < n → ¬ m ≡ n
<→¬≡ {m}{n} m<n = ≄→¬≡ (<→¬≃ m<n)

<→⋖ : m < n → m ⋖ n
<→⋖ {m}{n} mn = (<-weaken {m}{n} mn) , (<→¬≃ mn)

¬<→¬⋖ : ¬ (m < n) → ¬ (m ⋖ n)
¬<→¬⋖ {m} {n} ¬mn ((zero , mn) , ¬m≃n) = ¬m≃n (*≡* mn)
¬<→¬⋖ {m} {n} ¬mn ((suc d , mn) , ¬m≃n) =
  ¬mn (ℤ.<-+pos-trans {(↥ m) ℤ.· (↧ n)} {d}{(↥ n) ℤ.· (↧ m)} (zero , mn))

¬⋖→¬< : ¬ (m ⋖ n) → ¬ (m < n)
¬⋖→¬< = converse <→⋖

<Stable : Stable (m < n)
<Stable {m}{n} ¬¬m<n = ℤ.<Stable (↥ m ℤ.· ↧ n) (↥ n ℤ.· ↧ m) ¬¬m<n

⋖→< : m ⋖ n → m < n
⋖→< {m}{n} mn = <Stable {m}{n} (converse ¬<→¬⋖ (λ z → z mn))

⋖Dec : ∀ m n → Dec (m ⋖ n)
⋖Dec m n with ≤Dec m n | ≃Dec m n
... | yes m | yes n = no (λ z → z .snd n)
... | yes m | no ¬n = yes (m , ¬n)
... | no ¬m | yes n = no (λ z → ¬m (z .fst))
... | no ¬m | no ¬n = no (λ z → ¬m (z .fst))

<Dec : ∀ (m n : ℚ) → Dec (m < n)
<Dec m n with ⋖Dec m n
... | yes p = yes (⋖→< p)
... | no ¬p = no (converse <→⋖ ¬p)

isProp< : ∀ m n → isProp (m < n)
isProp< m n = ℤ.isProp<

isProp⋖ : ∀ m n → isProp (m ⋖ n)
isProp⋖ m n mn mn' = isProp× (m ≤ n) (¬ m ≃ n) ℤ.isProp≤ (isProp¬ (m ≃ n)) mn mn'

m≤n→¬n<m : ∀ {m n} → m ≤ n → ¬ (n < m)
m≤n→¬n<m {m}{n} mn =
  converse (ℤ.isAsym< {↥ n ℤ.· ↧ m} {↥ m ℤ.· ↧ n}) λ z → z mn

¬m<n→n≤m : ∀ {m n : ℚ} → ¬ (m < n) → n ≤ m
¬m<n→n≤m {m}{n} ¬mn with (↥ m ℤ.· ↧ n) ℤ.≟ (↥ n ℤ.· ↧ m)
... | ℤ.lt x = ⊥.elim (¬mn x)
... | ℤ.eq x = zero , sym x
... | ℤ.gt x = ℤ.<-weaken x

¬m≤n→n<m : ∀ {m n : ℚ} → ¬ (m ≤ n) → n < m
¬m≤n→n<m {m}{n} ¬m≤n = ⋖→< {n}{m}
  (¬m<n→n≤m {m}{n} (converse (<-weaken {m}{n}) ¬m≤n) ,
   sym≄ (¬*≡* (ℤ¬≤→¬≡ ¬m≤n)))

¬m≤n→n≤m : ∀ {m n : ℚ} → ¬ (m ≤ n) → n ≤ m
¬m≤n→n≤m {m}{n} nmn = <-weaken {n}{m} (¬m≤n→n<m {m}{n} nmn)

m<n→¬n≤m : ∀ {m n : ℚ} → m < n → ¬ (n ≤ m)
m<n→¬n≤m {m}{n} mn = converse (m≤n→¬n<m {n} {m}) (λ z → z mn)

m≤n→n≤m→m≃n : ∀ {m n} → m ≤ n → n ≤ m → m ≃ n
m≤n→n≤m→m≃n {m}{n} m≤n n≤m = *≡* (ℤ.isAntisym≤ m≤n n≤m)

m≤n→n≤m→m≡n : ∀ {m n} → m ≤ n → n ≤ m → m ≡ n
m≤n→n≤m→m≡n {m}{n} m≤n n≤m = ≃→≡ (m≤n→n≤m→m≃n {m}{n} m≤n n≤m)

m⋖n→¬n⋖m : ∀ {m n} → m ⋖ n → ¬ (n ⋖ m)
m⋖n→¬n⋖m {m}{n} m⋖n n⋖m = (snd m⋖n) (m≤n→n≤m→m≃n  (m⋖n .fst) (n⋖m .fst))

m<n→¬n<m : ∀ {m n} → m < n → ¬ (n < m)
m<n→¬n<m {m}{n} m<n = ¬⋖→¬< {n}{m} (m⋖n→¬n⋖m (<→⋖ m<n))

≤-diff : ∀ {m n} → m ≤ n → Σ[ d ∈ ℚ ] (m + d ≡ n) × NonNegative d
≤-diff {m}{n} (k , eqn) = d , (lhs ∙ step ∙ ·IdR n , tt)
  where
    d = [ pos k , ↧₊₁ n ·₊₁ ↧₊₁ m ]
    lhs : m + d ≡ [ (↥ m) ℤ.· (↧ n) , (↧₊₁ n) ·₊₁ (↧₊₁ m) ] + d
    lhs = cong (λ a → a + d)
      (sym (·IdR m) ∙
      cong₂ (λ a b → a · b) (≡↥↧₊₁ m) (sym (↧↧₊₁≡1 n)) ∙
      (·ᵘ-def-cross (↥ m) (↧ n) (↧₊₁ m) (↧₊₁ n)))
    step : [ (↥ m) ℤ.· (↧ n) , (↧₊₁ n) ·₊₁ (↧₊₁ m) ] + d ≡ n · 1ℚ
    step =
      (+overSameDenominator ((↥ m) ℤ.· (↧ n)) (pos k) (↧₊₁ n ·₊₁ ↧₊₁ m)) ∙
      (cong (λ a → [ a ,  ↧₊₁ n ·₊₁ ↧₊₁ m ]) eqn) ∙
      sym (·ᵘ-def (↥ n) (↧ m) (↧₊₁ n) (↧₊₁ m)) ∙
      cong₂ (λ a b → a · b) (sym (≡↥↧₊₁ n)) (↧↧₊₁≡1 m)

<-diff : ∀ {m n} → m < n → Σ[ d ∈ ℚ ] (m + d ≡ n) × Positive d
<-diff {m} {n} mn@(d-1 , eqn) =
  d , (fst (snd step) , nonZ→NonNeg→Pos dnz tt)
  where
    d = [ pos (suc d-1) , ↧₊₁ n ·₊₁ ↧₊₁ m ]
    dnz : NonZero d
    dnz = numSucNonZero {d-1} {↧₊₁ n ·₊₁ ↧₊₁ m}
    step : Σ ℚ (λ d → (m + d ≡ n) × NonNegative d)
    step = ≤-diff {m}{n} (<-weaken {m}{n} mn)

diff-≤ : ∀ {m n} → Σ[ d ∈ ℚ ] (m + d ≡ n) × NonNegative d → m ≤ n
diff-≤ {m} {n} mdn@(d@((num , den-1) , c) , m+d≡n , nonegd) with ≤Dec m n
... | yes p = p
... | no ¬p = ⊥.elim (Negative→NonNegative→⊥ contra m≥n)
  where
    n<m = ¬m≤n→n<m {m}{n} ¬p
    diff = <-diff {n}{m} n<m
    d' = diff .fst
    d'≡m-n = subtractR {d'}{n}{m} (+Comm d' n ∙ (diff .snd .fst))
    m<n : Positive (m - n)
    m<n = subst Positive d'≡m-n (diff .snd .snd)
    d≡n-m = subtractR {d}{m}{n} (+Comm d m ∙ m+d≡n)
    m≥n : NonNegative (n - m)
    m≥n = subst NonNegative d≡n-m nonegd
    contra : Negative (n - m)
    contra = subst (λ x → Negative x) (-dist- m n) (Positive→Negative- m<n)

diff-< : ∀ {m n} → Σ[ d ∈ ℚ ] (m + d ≡ n) × Positive d → m < n
diff-< {m}{n} mdn@(d@((num , den-1) , c) , m+d≡n , posd) with <Dec m n
... | yes p = p
... | no ¬p = ⊥.elim (Negative→NonNegative→⊥ contra m<n)
  where
    n≤m : n ≤ m
    n≤m = ¬m<n→n≤m {m}{n} ¬p
    diff = ≤-diff {n}{m} n≤m
    d' = diff .fst
    m+d'≡n : n + d' ≡ m
    m+d'≡n = diff .snd .fst
    step1 : d' ≡ m - n
    step1 = subtractR {d'}{n}{m} (+Comm d' n ∙ m+d'≡n)
    m<n : NonNegative (m - n)
    m<n = subst NonNegative step1 (diff .snd .snd)
    step2 : d ≡ n - m
    step2 = subtractR {d}{m}{n} (+Comm d m ∙ m+d≡n)
    m>n : Positive (n - m)
    m>n = subst Positive step2 posd
    contra : Negative (m - n)
    contra = subst (λ x → Negative x) (-dist- n m)
      (Positive→Negative- m>n)

isRefl≤ : ∀ m → m ≤ m
isRefl≤ m = zero , refl

isAntisym≤ : ∀ {m n} → m ≤ n → n ≤ m → m ≡ n
isAntisym≤ {m}{n} m≤n n≤m = ≃→≡ (m≤n→n≤m→m≃n m≤n n≤m)

isTrans≤ : m ≤ n → n ≤ o → m ≤ o
isTrans≤ {m}{n}{o} m≤n n≤o =
  diff-≤ {m}{o} ((d + d') , (m+d+d'≡o , +NonNegatives {d}{d'} tt tt))
  where
    d = fst (≤-diff {m}{n} m≤n) ; d' = fst (≤-diff {n}{o} n≤o)
    m+d≡n = (≤-diff {m}{n} m≤n) .snd .fst
    n+d'≡o = (≤-diff {n}{o} n≤o) .snd .fst
    m+d+d'≡o = +Assoc m d d' ∙ (cong (λ a → a + d') m+d≡n) ∙ n+d'≡o

≤Monotone+ : {s : ℚ} → m ≤ n → o ≤ s → m + o ≤ n + s
≤Monotone+ {m}{n}{o}{s} mn os = diff-≤ {m + o} {n + s} diffms
  where
    diffmn : Σ ℚ (λ d → (m + d ≡ n) × NonNegative d)
    diffmn = ≤-diff {m}{n} mn
    diffos : Σ ℚ (λ d' → (o + d' ≡ s) × NonNegative d')
    diffos = ≤-diff {o}{s} os
    d = fst diffmn ; d' = fst diffos
    m+d≡n = fst (snd diffmn) ; d'+o≡s = fst (snd diffos)
    mod≡ns : (m + d) + (o + d') ≡ n + s
    mod≡ns i = m+d≡n i + d'+o≡s i
    d+d' = +NonNegatives {d}{d'} tt tt
    diffms : Σ ℚ (λ d'' → ((m + o) + d'' ≡ (n + s)) × NonNegative d'')
    diffms = d + d' , a+b+'c+d≡a+c+'b+d m o d d' ∙ mod≡ns , d+d'

zero-≤NonNeg : ∀ {m} → NonNegative m → 0ℚ ≤ m
zero-≤NonNeg {m} nnm = diff-≤ {0ℚ}{m} (m , (+IdL m , nnm))

≤-+o : m ≤ n → m + o ≤ n + o
≤-+o {m}{n}{o} mn@(k , eqn) = diff-≤ {m + o} {n + o} (d , (step , tt))
  where
    diff = ≤-diff {m}{n} mn
    d = diff .fst
    step : (m + o) + d ≡ n + o
    step = (((m + o) + d) ≡⟨ sym (+Assoc m o d) ⟩
           m + (o + d) ≡⟨ cong (m +_) (+Comm o d) ⟩
           m + (d + o) ≡⟨ +Assoc m d o ⟩
           (m + d) + o ≡⟨ cong (_+ o) (fst (snd diff)) ⟩
           n + o ∎)

≤SumRightNonNeg : ∀ {m}{n} → NonNegative m → n ≤ m + n
≤SumRightNonNeg {m}{n} nnm = step3 step2 step1
  where
    step1 : 0ℚ + n ≤ m + n
    step1 =  ≤-+o {0ℚ}{m}{n} (zero-≤NonNeg {m} nnm)
    step2 : n ≤ 0ℚ + n
    step2 = weaken≡→≤ (sym (+IdL n))
    step3 = isTrans≤ {n} {0ℚ + n}{m + n}

≤-+NonNeg-trans : ∀ {m}{n}{o} → NonNegative o → m + o ≤ n → m ≤ n
≤-+NonNeg-trans {m}{n}{o} nno p = isTrans≤ {m}{m + o}{n} m≤m+o p
  where
    m≤o+m = ≤SumRightNonNeg {o}{m} nno
    m≤m+o = isTrans≤ {m}{o + m}{m + o} m≤o+m (weaken≡→≤ (+Comm o m))

≤-NonNeg+-trans : ∀ {m}{n}{o} → NonNegative o → o + m ≤ n → m ≤ n
≤-NonNeg+-trans {m}{n}{o} nno p = isTrans≤ {m}{o + m}{n} m≤o+m p
  where
    m≤o+m = ≤SumRightNonNeg {o}{m} nno

≤-o+ : m ≤ n → o + m ≤ o + n
≤-o+ {m} {n} {o} mn@(k , eqn) = subst (λ x → x)
  (cong₂ (λ a b → a ≤ b) (+Comm m o) (+Comm n o)) (≤-+o {m}{n}{o} mn)

≤-o+-cancel : o + m ≤ o + n → m ≤ n
≤-o+-cancel {o}{m}{n} ineq =
  diff-≤ {m}{n} (d , +CancelL o (m + d) n o+m+'d≡o+n , (snd (snd diff)))
  where
    diff : Σ ℚ (λ d → ((o + m) + d ≡ o + n) × NonNegative d)
    diff = ≤-diff {o + m}{o + n} ineq
    d = diff .fst
    o+m+'d≡o+n : o + (m + d) ≡ o + n
    o+m+'d≡o+n = +Assoc o m d ∙ fst (snd diff)

≤-+o-cancel : ∀ {m}{n}{o} → m + o ≤ n + o → m ≤ n
≤-+o-cancel {m}{n}{o} mn = ≤-o+-cancel {o}{m}{n} (subst (λ z → z) step mn)
  where
    step = cong₂ (λ a b → a ≤ b) (+Comm m o) (+Comm n o)

≤-·o : ∀ {m}{n}{o} → NonNegative o → m ≤ n → m · o ≤ n · o
≤-·o {m}{n}{o} nno mn = diff-≤ {m · o}{n · o} ((d · o) , (m·o+d·o≡n·o , nndo))
  where
    diff = ≤-diff {m}{n} mn
    d = fst diff
    m+d≡n = fst (snd diff)
    m·o+d·o≡n·o = sym (·DistL+ m d o) ∙ (cong (λ a → a · o) m+d≡n)
    nndo = ·NonNegatives {d}{o} tt nno

---------------------------------------
-- min and max

infixl 7 _⊓_
infixl 6 _⊔_

-- Min
_⊓_ : ℚ → ℚ → ℚ
p ⊓ q with (≤Dec p q)
... | yes p' = p
... | no q' = q

min = _⊓_

-- Max
_⊔_ : ℚ → ℚ → ℚ
p ⊔ q with (≤Dec p q)
... | yes p' = q
... | no q' = p

max = _⊔_

-- Properties of Min and Max

minIdem : ∀ (m : ℚ) → min m m ≡ m
minIdem m with ≤Dec m m
... | yes p = refl
... | no ¬p = refl

maxIdem : ∀ (m : ℚ) → max m m ≡ m
maxIdem m with ≤Dec m m
... | yes p = refl
... | no ¬p = refl

minComm : ∀ m n → min m n ≡ min n m
minComm m n with ≤Dec m n | ≤Dec n m
... | yes p | yes q = isAntisym≤ {m}{n} p q
... | yes p | no ¬q = refl
... | no ¬p | yes q = refl
... | no ¬p | no ¬q = ⊥.elim {A = λ x → n ≡ m}
  (m⋖n→¬n⋖m {m}{n} (<→⋖ (¬m≤n→n<m {n}{m} ¬q)) (<→⋖ (¬m≤n→n<m {m}{n} ¬p)))

maxComm : ∀ m n → max m n ≡ max n m
maxComm m n with ≤Dec m n | ≤Dec n m
... | yes p | yes q = m≤n→n≤m→m≡n q p
... | yes p | no ¬q = refl
... | no ¬p | yes q = refl
... | no ¬p | no ¬q = ⊥.elim {A = λ x → m ≡ n} (¬q step)
  where
    step : n ≤ m
    step = <-weaken {n}{m} (¬m≤n→n<m {m}{n} ¬p)

≤→⊓ : ∀ {p q : ℚ} → p ≤ q → p ⊓ q ≡ p
≤→⊓ {p}{q} pq with ≤Dec p q
... | yes r = refl
... | no ¬r = ⊥.elim {A = λ x → q ≡ p} (¬r pq)

¬≤→⊓ : ∀ {p q : ℚ} → ¬ (p ≤ q) → p ⊓ q ≡ q
¬≤→⊓ {p}{q} pq with ≤Dec p q
... | yes r = ⊥.elim (pq r)
... | no ¬r = refl

⊓→≤ : ∀ {p q : ℚ} → p ⊓ q ≡ p → p ≤ q
⊓→≤ {p}{q} pq with ≤Dec p q
... | yes r = r
... | no ¬r = zero , *≡*⁻¹ (≡→≃ (sym pq))

≤→⊔ : ∀ {p q : ℚ} → p ≤ q → p ⊔ q ≡ q
≤→⊔ {p}{q} pq with ≤Dec p q
... | yes r = refl
... | no ¬r = ⊥.elim {A = λ x → p ≡ q} (¬r pq)

¬≤→⊔ : ∀ {p q : ℚ} → ¬ (p ≤ q) → p ⊔ q ≡ p
¬≤→⊔ {p}{q} npq = maxComm p q ∙ rhs
  where
    rhs : q ⊔ p ≡ p
    rhs = ≤→⊔ {q}{p} (<-weaken {q}{p} (¬m≤n→n<m {p}{q} npq))

⊔→≤ : ∀ {p q : ℚ} → p ⊔ q ≡ p → q ≤ p
⊔→≤ {p}{q} pq with ≤Dec p q
... | yes r = weaken≡→≤ pq
... | no ¬r = <-weaken {q}{p} (¬m≤n→n<m {p}{q} ¬r)

private
  minAssocHlp : ∀ {m : ℚ}{n : ℚ}{o : ℚ} →
    (mn : Dec (m ≤ n)) (no' : Dec (n ≤ o)) (mo : Dec (m ≤ o)) →
     min m (min n o) ≡ min (min m n) o
  minAssocHlp {m}{n}{o} (yes p) (yes q) _ = lhs ∙ sym rhs
    where
      m⊓n≡m = ≤→⊓ {m}{n} p
      lhs = cong (λ a → min m a) (≤→⊓ {n}{o} q) ∙ m⊓n≡m
      rhs = cong (λ a → min a o) m⊓n≡m ∙
        ≤→⊓ (isTrans≤ {m}{n}{o} p q)
  minAssocHlp {m}{n}{o} (yes p) (no ¬q) (yes r) = lhs ∙ sym rhs
    where
      lhs = cong (λ a → min m a ) (¬≤→⊓ {n}{o} ¬q) ∙ ≤→⊓ r
      rhs = cong (λ a → min a o) (≤→⊓ {m}{n} p) ∙ ≤→⊓ r
  minAssocHlp {m}{n}{o} (yes p) (no ¬q) (no ¬r) = lhs ∙ sym rhs
    where
      rhs = cong (λ a → min a o) (≤→⊓ {m}{n} p) ∙ ¬≤→⊓ {m}{o} ¬r
      lhs = cong (λ a → min m a) (¬≤→⊓ {n}{o} ¬q) ∙ ¬≤→⊓ ¬r
  minAssocHlp {m}{n}{o} (no ¬p) (yes q) _ = lhs ∙ sym rhs
    where
      n⊓o≡n = ≤→⊓ {n}{o} q
      m⊓n≡n = ¬≤→⊓ {m}{n} ¬p
      lhs = cong (λ a → min m a) n⊓o≡n ∙ m⊓n≡n
      rhs = cong (λ a → min a o) m⊓n≡n ∙ n⊓o≡n
  minAssocHlp {m}{n}{o} (no ¬p) (no ¬q) _ = lhs ∙ sym rhs
   where
      n⊓o≡o = ¬≤→⊓ {n}{o} ¬q
      o≤m = isTrans≤ {o}{n}{m} (¬m≤n→n≤m {n}{o} ¬q) (¬m≤n→n≤m {m}{n} ¬p)
      lhs = cong (λ a → min m a) n⊓o≡o ∙ minComm m o ∙ ≤→⊓ {o}{m} o≤m
      rhs = cong (λ a → min a o) (¬≤→⊓ {m}{n} ¬p) ∙ n⊓o≡o

minAssoc : ∀ m n o → min m (min n o) ≡ min (min m n) o
minAssoc m n o = minAssocHlp {m}{n}{o} (≤Dec m n) (≤Dec n o) (≤Dec m o)

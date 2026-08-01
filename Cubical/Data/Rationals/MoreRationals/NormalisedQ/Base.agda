module Cubical.Data.Rationals.MoreRationals.NormalisedQ.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism using (isoToPath ; iso)
open import Cubical.Foundations.HLevels using (isSetΣ ; isSet×)
open import Cubical.Foundations.Transport
open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary
open BinaryRelation
open isEquivRel
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Data.Sigma using (_×_; Σ≡Prop)
open import Cubical.Data.Nat as ℕ
  using (ℕ; discreteℕ; znots; snotz; m+n≡0→m≡0×n≡0; +-suc;
   ·-suc;  _∸_; suc; zero ; predℕ; suc-predℕ; isSetℕ; injSuc;
   ¬x≡0→NonZero; ¬k·l≡0→¬k≡0)
open import Cubical.Data.Nat.GCD as ℕ
open import Cubical.Data.Nat.Coprime as ℕ
open import Cubical.Data.NatPlusOne using (1+_; ℕ₊₁; -1+_; ℕ₊₁→ℕ; _·₊₁_)
open import Cubical.Data.NatPlusOne.PropertiesWithInt
open import Cubical.Data.Int as ℤ
  renaming (_+_ to _ℤ+_; _-_ to _ℤ-_; -_ to -ℤ_; _·_ to _ℤ·_; abs to absℤ)
open import Cubical.Data.Int.GCD as ℤ using (gcd-def; ℕ₊₁→ℤ-gcd-def; gcdSucNot0)
open import Cubical.Data.Int.Order as ℤ using ()

converse : {ℓ : Level} {a b : Type ℓ} →
  (a → b) → ¬ b → ¬ a
converse = λ z z₁ z₂ → z₁ (z z₂)

------------------------------------------------
-- Core definitions

-- ℚ as the set of coprime pairs in ℤ × ℕ (where the ℕ is d-1)
-- Essentially reproduces reduced Rationals ℚ as in regular Agda,
-- but the Coprime is handled cubically and ℤ is Cubical.Data.Int.

ℚ : Type
ℚ = Σ (ℤ × ℕ) λ q → areCoprime ((absℤ (fst q)) , suc (snd q))

isSetℚ : isSet ℚ
isSetℚ = isSetΣ (isSet× isSetℤ isSetℕ) (λ _ → isProp→isSet isPropIsGCD)

-- numerator ℤ
↥_ : ℚ → ℤ
↥ ((z , n) , copr) = z

-- denominator as ℤ (always greater than 0)
↧_ : ℚ → ℤ
↧ ((z , n) , copr) = pos (suc n)

sign↧ : ∀ (q : ℚ) → sign (↧ q) ≡ pos 1
sign↧ q@((z , n) , c) = refl

sign↥p·↧q≡sign↥p : ∀ p q → sign ((↥ p) ℤ.· (↧ q)) ≡ sign (↥ p)
sign↥p·↧q≡sign↥p p@((z , n) , c) q@((z' , n') , c') =
  signx·y≡signx·signy (↥ p) (↧ q) ∙ ·IdR (sign (↥ p))

-- denominator-1 as ℕ
↧₋₁_ : ℚ → ℕ
↧₋₁ ((z , n) , copr) = n

-- denominator as ℕ₊₁
↧₊₁_ : ℚ → ℕ₊₁
↧₊₁ ((z , n) , copr) = 1+ n

↧≡↧→↧₋₁≡↧₋₁ : ∀ {x y : ℚ} → ↧ x ≡ ↧ y → ↧₋₁ x ≡ ↧₋₁ y
↧≡↧→↧₋₁≡↧₋₁ d = ℕ.injSuc (ℤ.injPos d)

x≡y→↥x≡↥y : ∀ {x y : ℚ} → x ≡ y → ↥ x ≡ ↥ y
x≡y→↥x≡↥y {x}{y} xy = cong (λ u → ↥ u) xy

x≡y→↧x≡↧y : ∀ {x y : ℚ} → x ≡ y → ↧ x ≡ ↧ y
x≡y→↧x≡↧y {x}{y} xy = cong (λ u → ↧ u) xy

x≡y→↧₊₁x≡↧₊₁y : ∀ {x y : ℚ} → x ≡ y → ↧₊₁ x ≡ ↧₊₁ y
x≡y→↧₊₁x≡↧₊₁y {x}{y} xy = cong (λ u → ↧₊₁ u) xy

x≡y→↧₋₁x≡↧₋₁y : ∀ {x y : ℚ} → x ≡ y → ↧₋₁ x ≡ ↧₋₁ y
x≡y→↧₋₁x≡↧₋₁y {x}{y} xy = cong (λ u → ↧₋₁ u) xy

↥↧₋₁ : ℚ → (ℤ × ℕ)
↥↧₋₁ q = ↥ q , ↧₋₁ q

↥↧₊₁ : ℚ → (ℤ × ℕ₊₁)
↥↧₊₁ q = ↥ q , ↧₊₁ q

↥↧ : ℚ → (ℤ × ℤ)
↥↧ q = ↥ q , ↧ q

-- Uniqueness of the reduced numerator/denominator pair
ℚ-unique₋₁ : ∀ {x y : ℚ} → ↥ x ≡ ↥ y → ↧₋₁ x ≡ ↧₋₁ y → x ≡ y
ℚ-unique₋₁ {x} {y} n d-1 = Σ≡Prop (λ u → isPropIsGCD) λ i → (n i) , (d-1 i)

ℚ-unique₊₁ : ∀ {x y : ℚ} → ↥ x ≡ ↥ y → ↧₊₁ x ≡ ↧₊₁ y → x ≡ y
ℚ-unique₊₁ {x} {y} n d = ℚ-unique₋₁ n (cong -1+_ d)

-- Numerator and denominator determine equality
ℚ-unique : ∀ {x y : ℚ} → ↥ x ≡ ↥ y → ↧ x ≡ ↧ y → x ≡ y
ℚ-unique {x}{y} n d-1 = ℚ-unique₋₁ n (↧≡↧→↧₋₁≡↧₋₁ {x}{y} d-1)

-----------------------------------------------
-- Negation
infix  8 -_
-_ : ℚ → ℚ
- a@((pos zero , d-1) , c) = a
- ((pos (suc n) , d-1) , c) = ((negsuc n) , d-1) , c
- ((negsuc n , d-1) , c) = (pos (suc n) , d-1) , c

-- Properties of -_

↥-neg : ∀ a → ↥ (- a) ≡ -ℤ (↥ a)
↥-neg ((pos zero , d-1) , c) = refl
↥-neg ((pos (suc n) , d-1) , c) = refl
↥-neg ((negsuc n , d-1) , c) = refl

↧-neg : ∀ a → ↧ (- a) ≡ ↧ a
↧-neg ((pos zero , d-1) , c) = refl
↧-neg ((pos (suc n) , d-1) , c) = refl
↧-neg ((negsuc n , d-1) , c) = refl

↧₋₁-neg : ∀ (a : ℚ) → ↧₋₁ (- a) ≡ ↧₋₁ a
↧₋₁-neg a = ↧≡↧→↧₋₁≡↧₋₁ {(- a)} {a} (↧-neg a)

↧₊₁-neg : ∀ (a : ℚ) → ↧₊₁ (- a) ≡ ↧₊₁ a
↧₊₁-neg a = cong 1+_ (↧₋₁-neg a)

neg-distr↥ : ∀ {x} {y} → ↥ (- x) ≡ (↥ y) → ↧₋₁ x ≡ ↧₋₁ y → - x ≡ y
neg-distr↥ {x}{y} numerators denominators =
  ℚ-unique₋₁ numerators ((↧₋₁-neg x) ∙ denominators )

neg-distr↥↧₋₁ : ∀ x → ↥↧₋₁ (- x) ≡ (-ℤ (↥ x) , ↧₋₁ x)
neg-distr↥↧₋₁ x = cong₂ (λ a b → (a , b)) (↥-neg x) (↧₋₁-neg x)

↥x+↥-x≡0 : ∀ x → (↥ x) ℤ.+ ↥ (- x) ≡ 0
↥x+↥-x≡0 x =  cong ((↥ x) ℤ.+_) (↥-neg x) ∙ -Cancel (↥ x)

neg-involutive : ∀{a} → - (- a) ≡ a
neg-involutive {(pos zero , d-1) , c} = refl
neg-involutive {(pos (suc n) , d-1) , c} = refl
neg-involutive {(negsuc zero , d-1) , c} = refl
neg-involutive {(negsuc (suc n) , d-1) , c} = refl

neg-injective : ∀{a}{b} → - a ≡ - b → a ≡ b
neg-injective {a}{b} -a-b =
  sym (neg-involutive {a}) ∙ (cong (-_) -a-b) ∙ neg-involutive {b}

-------------------------------------------------
-- Constructing rationals

normalise : ℕ → ℕ₊₁ → ℚ
normalise m n = let numden = toCoprime (m , n) in
  ((pos (fst numden)) , -1+ (snd numden)) , toCoprimeAreCoprime (m , n)

normalise-id : (m : ℕ) → (n : ℕ₊₁) → let numden = toCoprime (m , n) in
  normalise m n ≡
   (((pos (fst numden)) , -1+ (snd numden)) , toCoprimeAreCoprime (m , n))
normalise-id m n = refl

-- Constructors for ℚ that take two numbers, say -6 and 21,
-- and returns them in normalized form, e.g, -2 and 7.
[_] : (ℤ × ℕ₊₁) → ℚ
[ pos m , n ] = normalise m n
[ negsuc m , n ] = - normalise (suc m) n

-- Some constants
0ℚ : ℚ
0ℚ = [ 0 , 1 ]

1ℚ : ℚ
1ℚ = [ 1 , 1 ]

-1ℚ : ℚ
-1ℚ = [ -1 , 1 ]

½ : ℚ
½ = [ 1 , 2 ]

-½ : ℚ
-½ = - ½

ℤ→ℚ : ℤ → ℚ
ℤ→ℚ z = [ z , 1 ]

----------------------------------------------------

-- About 0ℚ

↥a≡0→a≡0ℚ : {a : ℚ} → ↥ a ≡ 0 → a ≡ 0ℚ
↥a≡0→a≡0ℚ {a@((z , d-1) , c)} a0 = ℚ-unique₋₁ a0 (ℕ.injSuc (zeroCoprime' copr))
  where
    copr = transport (cong (λ u → areCoprime (u , suc d-1)) (cong absℤ a0)) c

↥0→↧₋₁0 : {a : ℚ} → ↥ a ≡ 0 → ↧₋₁ a ≡ 0
↥0→↧₋₁0 {a@((n , d-1) , c)} a0 = ℕ.injSuc (zeroCoprime' copr)
  where
    copr = transport (cong (λ u → areCoprime (u , suc d-1)) (cong absℤ a0)) c

↥0→↧1 : {a : ℚ} → ↥ a ≡ 0 → ↧ a ≡ 1
↥0→↧1 {a} a0 = cong (λ u → pos (suc u)) (↥0→↧₋₁0 {a} a0)

0-id : ∀ {n}{c} → ((pos zero , n) , c) ≡ 0ℚ
0-id {n}{c} = ↥a≡0→a≡0ℚ refl

a≡0→↥a≡0 :{a : ℚ} → a ≡ 0ℚ → ↥ a ≡ 0
a≡0→↥a≡0 {((n , d-1) , c)} a0 = cong ↥_ a0

↥a≡↥b≡0⇒a≡b : ∀ {a} {b} → ↥ a ≡ 0 → ↥ b ≡ 0 → a ≡ b
↥a≡↥b≡0⇒a≡b {a@((n , d-1) , c)} {b@((n' , d-1') , c')} a0 b0 =
  (↥a≡0→a≡0ℚ a0) ∙ sym (↥a≡0→a≡0ℚ b0)

-- equality depends on numerator and denominator
↥↧₊₁a≡↥↧₊₁b→a≡b : ∀ {a}{b} → ↥↧₊₁ a ≡ ↥↧₊₁ b → a ≡ b
↥↧₊₁a≡↥↧₊₁b→a≡b {a}{b} ab = ℚ-unique₊₁ (cong fst ab) (cong snd ab)

↥↧₋₁a≡↥↧₋₁b→a≡b : ∀ {a}{b} → ↥↧₋₁ a ≡ ↥↧₋₁ b → a ≡ b
↥↧₋₁a≡↥↧₋₁b→a≡b {a}{b} ab = ℚ-unique₋₁ (cong fst ab) (cong snd ab)

↥↧a≡↥↧b→a≡b : ∀ {a}{b} → ↥↧ a ≡ ↥↧ b → a ≡ b
↥↧a≡↥↧b→a≡b {a}{b} ab = ℚ-unique (cong fst ab) (cong snd ab)


---------------------------------------------------
-- Signs

NonZero : (p : ℚ) → Type
NonZero ((pos zero , d-1) , c) = ⊥
NonZero ((pos (suc n) , d-1) , c) = Unit
NonZero ((negsuc n , d-1) , c) = Unit

IsZero : (p : ℚ) → Type
IsZero ((pos zero , n) , c) = Unit
IsZero ((pos (suc m) , n) , c) = ⊥
IsZero ((negsuc m , n) , c) = ⊥

¬IsZero→NonZero : ∀ p → ¬ (IsZero p) → NonZero p
¬IsZero→NonZero ((pos zero , n) , c) ¬p0 = ¬p0 tt
¬IsZero→NonZero ((pos (suc m) , n) , c) ¬p0 = tt
¬IsZero→NonZero ((negsuc m , n) , c) ¬p0 = tt

Positive : (p : ℚ) → Type
Positive ((pos zero , d-1) , c) = ⊥
Positive ((pos (suc n) , d-1) , c) = Unit
Positive ((negsuc n , d-1) , c) = ⊥

Negative : (p : ℚ) → Type
Negative ((pos n , d-1) , c) = ⊥
Negative ((negsuc n , d-1) , c) = Unit

NonNegative : (p : ℚ) → Type
NonNegative ((pos m , n) , copr) = Unit
NonNegative ((negsuc m , n) , copr) = ⊥

IsZero→NonNegative : {p : ℚ} → IsZero p → NonNegative p
IsZero→NonNegative {(pos m , n) , c} posp = tt

Positive→NonNegative : ∀ {p : ℚ} → Positive p → NonNegative p
Positive→NonNegative {(pos m , n) , c} pp = tt
Positive→NonNegative {(negsuc m , n) , c} pp = pp

IsInteger : (p : ℚ) → Type
IsInteger ((z , zero) , c) = Unit
IsInteger ((z , suc n) , c) = ⊥

decIsZero : ∀ (p : ℚ) → Dec (IsZero p)
decIsZero p@((pos zero , n) , c) = yes tt
decIsZero ((pos (suc m) , n) , c) = no (λ ())
decIsZero ((negsuc m , n) , c) = no (λ ())

decNonZero : ∀ (p : ℚ) → Dec (NonZero p)
decNonZero ((pos ℕ.zero , n) , copr) = no (λ ())
decNonZero ((pos (ℕ.suc m) , n) , copr) = yes tt
decNonZero ((negsuc m , n) , copr) = yes tt

decPositive : ∀ (p : ℚ) → Dec (Positive p)
decPositive ((pos zero , n) , copr) = no λ ()
decPositive ((pos (suc m) , n) , copr) = yes tt
decPositive ((negsuc m , n) , copr) = no (λ ())

decNegative : ∀ (p : ℚ) → Dec (Negative p)
decNegative ((pos m , n) , copr) = no (λ ())
decNegative ((negsuc m , n) , copr) = yes tt

decNonNegative : ∀ (p : ℚ) → Dec (NonNegative p)
decNonNegative ((pos m , n) , c) = yes tt
decNonNegative ((negsuc m , n) , c) = no (λ ())

decIsInteger : ∀ (p : ℚ) → Dec (IsInteger p)
decIsInteger ((z , zero) , c) = yes tt
decIsInteger ((z , suc n) , c) = no (λ ())

NonZero→¬≡0 : ∀ {p : ℚ} → NonZero p → ¬ p ≡ 0ℚ
NonZero→¬≡0 p@{(pos (suc m) , n) , c} tt =
  converse a≡0→↥a≡0 (λ x → snotz (injPos x))
NonZero→¬≡0 p@{(negsuc m , n) , c} tt =
  converse a≡0→↥a≡0 (λ x → ℤ.negsucNotpos m 0 x)

¬≡0→NonZero : ∀ {p : ℚ} → ¬ p ≡ 0ℚ → NonZero p
¬≡0→NonZero {(pos zero , n) , c} ¬p0 = ¬p0 (↥a≡0→a≡0ℚ refl)
¬≡0→NonZero {(pos (suc m) , n) , c} ¬p0 = tt
¬≡0→NonZero {(negsuc m , n) , c} ¬p0 = tt

---------------------------------------------
-- Abs
abs : ℚ → ℚ
abs z@((pos m , n) , copr) = z
abs z@((negsuc m , n) , copr) = ((pos (suc m) , n) , copr)

absDef : ∀ x → abs (- x) ≡ abs x
absDef ((pos zero , n) , copr) = refl
absDef ((pos (suc m) , n) , copr) = refl
absDef ((negsuc m , n) , copr) = refl

absNegative : ∀ x → Negative x → abs x ≡ - x
absNegative ((negsuc m , n) , c) negx = refl

absNonNegative : ∀ x → NonNegative x → abs x ≡ x
absNonNegative ((pos zero , n) , c) nnegx = refl
absNonNegative ((pos (suc m) , n) , c) nnegx = refl
absNonNegative ((negsuc m , n) , c) nnegx = ⊥.elim nnegx

absIsNonNegative : ∀ x → NonNegative (abs x)
absIsNonNegative ((pos zero , n) , c) = tt
absIsNonNegative ((pos (suc m) , n) , c) = tt
absIsNonNegative ((negsuc m , n) , c) = tt

----------------------------------------------------
-- Properties of normalise and [ _ ]

toCoprime→Normalise≡ : ∀ {x y u v} → toCoprime (x , y) ≡ toCoprime (u , v) →
  ↥↧₋₁ (normalise x y) ≡ ↥↧₋₁ (normalise u v)
toCoprime→Normalise≡ cc = cong (λ ab → forNormalise ab) cc
  where
    forNormalise : ∀ (ab : ℕ × ℕ₊₁) → ℤ × ℕ
    forNormalise (a , b) = (pos a , -1+ b)

↥↧₊₁-normalise : (m : ℕ) → (n : ℕ₊₁) → areCoprime (m , (ℕ₊₁→ℕ n)) →
  (↥↧₊₁ (normalise m n)) ≡ (pos m , n)
↥↧₊₁-normalise m (1+ n') copr = cong step1 step2
  where
    step1 : (ℕ × ℕ₊₁) → Σ ℤ (λ v → ℕ₊₁)
    step1 = (λ a → (pos (fst a) , (snd a)))
    step2 : (ToCoprime.c₁ (m , (1+ n')) , ToCoprime.c₂ (m , (1+ n'))) ≡
            (m , (1+ n'))
    step2 = toCoprime-idem (m , (1+ n')) copr

normalise-coprime : {m : ℕ} → {n : ℕ₊₁} →
  (copr : areCoprime (m , (ℕ₊₁→ℕ n))) →
    normalise m n ≡ ((pos m , -1+ n) , copr)
normalise-coprime {m}{n} copr = ↥↧₊₁a≡↥↧₊₁b→a≡b (↥↧₊₁-normalise m n copr)

normalise-coprime' : {m : ℕ} → {n : ℕ} →
  (copr : areCoprime (m , suc n)) →
    normalise m (1+ n) ≡ ((pos m , n) , copr)
normalise-coprime' {m}{n} copr = normalise-coprime copr

normaliseZero : ∀ n → normalise 0 n ≡ 0ℚ
normaliseZero n = ℚ-unique₋₁ refl (zeroCoprime (snd (normalise 0 n)))

normaliseNonZero : ∀ m n → ¬ (normalise (suc m) n ≡ 0ℚ)
normaliseNonZero m n x = coprime≢0 m n
  (ℤ.injPos ((cong (↥_) (normalise-id (suc m) n)) ∙ (cong ↥_ x)))

numerator[]≢0 : ∀ z {n+} → ¬ ([ z , n+ ] ≡ 0ℚ) → ¬ (z ≡ 0)
numerator[]≢0 (pos zero) {n+} ¬0 x =
  ⊥.elim {A = λ u → ⊥} (¬0 (normaliseZero n+))
numerator[]≢0 (pos (suc n)) {n+} ¬0 x =
  ⊥.elim {A = λ u → ⊥} (snotz (injPos x))
numerator[]≢0 (negsuc n) {n+} ¬0 x =
  ⊥.elim {A = λ u → ⊥} (negsucNotpos n zero x)

[0,n]≡0 : ∀ n → [ 0 , n ] ≡ 0ℚ
[0,n]≡0 n = normaliseZero n

[z,n]≡0→z≡0 : ∀ {z}{n} → [ z , n ] ≡ 0ℚ → z ≡ 0
[z,n]≡0→z≡0 {pos zero} {n} zn0 = refl
[z,n]≡0→z≡0 {pos (suc m)} {n} zn0 =
  ⊥.elim {A = λ x → pos (suc m) ≡ pos 0} (normaliseNonZero m n zn0)
[z,n]≡0→z≡0 {negsuc m} {n} zn0 =
  ⊥.elim {A = λ x → negsuc m ≡ pos 0}
   (normaliseNonZero m n ((sym neg-involutive) ∙ (cong -_ zn0) ))

[negsuc]≡[-pos] : ∀ n d → [ negsuc n , d ] ≡ - [ pos (suc n) , d ]
[negsuc]≡[-pos] n d = refl

[_]Def : ∀ {z}{n} copr → [ z , (1+ n) ] ≡ ((z , n) , copr)
[_]Def {pos m} {n} copr = normalise-coprime copr
[_]Def {negsuc m} {n} copr = cong -_ (normalise-coprime copr)

≡↥↧₊₁ : ∀ x → x ≡ [ ↥ x , ↧₊₁ x ]
≡↥↧₊₁ x@((z , n) , copr) = sym [ copr ]Def

gcd≡1→↥↧₊₁[x]≡x : ∀{z : ℤ}{n} →
  ℕ.gcd (absℤ z) (suc n) ≡ 1 → ↥↧₊₁ [ z , (1+ n) ] ≡ (z , 1+ n)
gcd≡1→↥↧₊₁[x]≡x {z}{n} zn1 = cong ↥↧₊₁ [ gcd≡→isGCD zn1 ]Def

·CancelR-normalise : ∀ ((m , n) : ℕ × ℕ₊₁) (k : ℕ₊₁) →
  normalise (m ℕ.· ℕ₊₁→ℕ k) (n ·₊₁ k) ≡ normalise m n
·CancelR-normalise (m , n) k =
  ↥↧₋₁a≡↥↧₋₁b→a≡b (toCoprime→Normalise≡ {m ℕ.· ℕ₊₁→ℕ k}{n ·₊₁ k}{m}{n}
    (toCoprime-cancelʳ (m , n) k))

-----------------------------------------------
-- Equality of rational numbers

infix 4 _≃_

data _≃_ : Rel ℚ ℚ ℓ-zero where
  *≡* : ∀ {p q} → (↥ p ℤ· ↧ q) ≡ (↥ q ℤ· ↧ p) → p ≃ q

_≄_ : Rel ℚ ℚ ℓ-zero
p ≄ q = ¬ (p ≃ q)

*≡*⁻¹ : ∀ {p : ℚ} {q : ℚ} → p ≃ q → ↥ p ℤ· ↧ q ≡ ↥ q ℤ· ↧ p
*≡*⁻¹ {p} {q} (*≡* x) = x

¬*≡* : ∀ {m}{n} → ¬ (↥ m) ℤ.· (↧ n) ≡ (↥ n) ℤ.· (↧ m) → ¬ m ≃ n
¬*≡* {m}{n} ¬mn = λ x → ¬mn (*≡*⁻¹ {m}{n} x)

isProp≃ : ∀ {p q} → isProp (p ≃ q)
isProp≃ {(n , d-1) , c} {(n' , d-1') , c'} (*≡* x) (*≡* y) = cong *≡*
  (isSetℤ (n ℤ· (↧ ((n' , d-1') , c'))) (n' ℤ· (↧ ((n , d-1) , c))) x y)

dec≃ : ∀ {p q} → Dec (p ≃ q)
dec≃ {p}{q} with discreteℤ (↥ p ℤ· ↧ q) (↥ q ℤ· ↧ p)
... | yes pq = yes (*≡* pq)
... | no ¬pq = no λ x → ¬pq (*≡*⁻¹ x)

≃Dec : ∀ (p q : ℚ) → Dec (p ≃ q)
≃Dec p q = dec≃ {p}{q}

≃-def : ∀ (p : ℚ) (q : ℚ) → (↥ p ℤ· ↧ q ≡ ↥ q ℤ· ↧ p) ≡ (p ≃ q)
≃-def p q = isoToPath
  (iso (*≡* {p}{q}) (*≡*⁻¹ {p}{q}) (λ b → isProp≃ (*≡* (*≡*⁻¹ b)) b)
  (λ a → isSetℤ ((↥ p) ℤ· (↧ q)) ((↥ q) ℤ· (↧ p))
   (*≡*⁻¹ {p}{q} (*≡* {p}{q} a)) a))

↥↧→≃ : ∀ {x}{y} → ↥ x ≡ ↥ y → ↧ x ≡ ↧ y → x ≃ y
↥↧→≃ nums dens = *≡* (cong₂ (ℤ._·_) nums (sym dens))

≡→≃ : ∀ {x} {y} → x ≡ y → x ≃ y
≡→≃ {x}{y} xy = ↥↧→≃ (cong (λ u → ↥ u) xy) (cong  (λ u → ↧ u) xy)

≄→¬≡ : ∀ {x} {y} → x ≄ y → ¬ (x ≡ y)
≄→¬≡ {x} {y} nxy = λ u → nxy (≡→≃ u)

p≃q→-p≃-q : ∀ {p}{q} → ↥ p ℤ.· ↧ q ≡ ↥ q ℤ.· ↧ p →
  ↥ (- p) ℤ.· ↧ (- q) ≡ ↥ (- q) ℤ.· ↧ (- p)
p≃q→-p≃-q {p}{q} pq = cong₂ (λ a b → a ℤ.· b) (↥-neg p) (↧-neg q) ∙
  sym (-DistL· (↥ p) (↧ q)) ∙ cong -ℤ_ pq ∙ -DistL· (↥ q) (↧ p) ∙
  sym (cong₂ (λ a b → a ℤ.· b) (↥-neg q) (↧-neg p))

↥p·↧q≡↥q·↧p'→↥↧p≡↥↧qPos : ∀ {m}{n}{m'}{n'}{c}{c'} →
  ↥ ((pos m , n) , c) ℤ· ↧ ((pos m' , n') , c') ≡
  ↥ ((pos m' , n') , c') ℤ· ↧ ((pos m , n) , c) →
  ↥↧ ((pos m , n) , c) ≡ ↥↧ ((pos m' , n') , c')
↥p·↧q≡↥q·↧p'→↥↧p≡↥↧qPos {zero} {n} {zero} {n'} {c} {c'} pq =
  cong ↥↧ (0-id {n}{c}) ∙ sym (cong ↥↧ (0-id {n'}{c'}))
↥p·↧q≡↥q·↧p'→↥↧p≡↥↧qPos {zero} {n} {suc m'} {n'} {c} {c'} pq =
  ⊥.elim {ℓ-zero}{λ x → ↥↧ ((pos zero , n) , c) ≡
   ↥↧ ((pos (suc m') , n') , c')}
  (snotz (injPos (sym (signx·y≡signx·signy
   (↥ ((pos (suc m') , n') , c')) (↧ ((pos zero , n) , c))) ∙
    sym (cong sign pq) ∙
     signx·y≡signx·signy (pos (zero)) (pos (suc n')))))
↥p·↧q≡↥q·↧p'→↥↧p≡↥↧qPos {suc m}{n}{zero}{n'}{c}{c'} pq =
  ⊥.elim {A = λ x → ↥↧ ((pos (suc m) , n) , c) ≡
   ↥↧ ((pos zero , n') , c')} (znots (ℤ.injPos ((sym (cong sign pq)) ∙
   (signx·y≡signx·signy (pos (suc m)) (pos (suc n'))))))
↥p·↧q≡↥q·↧p'→↥↧p≡↥↧qPos m@{suc p}{n} m'@{suc q}{n'}{c}{c'} pq i =
  (cong pos m≡m' i) , (cong (λ a → pos (suc a)) (sym n≡n') i)
  where
    ℕHlp : suc p ℕ.· suc n' ≡ suc q ℕ.· suc n
    ℕHlp = injPos
     ((pos·pos m (suc n') ∙ pq ∙ sym (pos·pos m' (suc n))))
    m≡m' = natDivisibility c c' ℕHlp
    n≡n' = injSuc (ℕ.inj-sm· {q}
     ((sym (cong (λ v → v ℕ.· suc n') m≡m')) ∙ ℕHlp))

≃→≡ : ∀ {p}{q} → p ≃ q → p ≡ q
≃→≡ {p@((pos m ,  n) , c)} {q@((pos m' ,  n') , c')} (*≡* pq) =
  ↥↧a≡↥↧b→a≡b (↥p·↧q≡↥q·↧p'→↥↧p≡↥↧qPos {c = c}{c' = c'} pq)
≃→≡ {p@((pos zero , n) , c)} {q@((negsuc m' , n') , c')} (*≡* pq) =
 ⊥.elim {A = λ x → p ≡ q} ((posNotnegsuc 0 0)
 (sym (sign↥p·↧q≡sign↥p p q) ∙ (cong sign pq) ∙ (sign↥p·↧q≡sign↥p q p)))
≃→≡ {p@((pos (suc m) , n) , c)} {q@((negsuc m' , n') , c')} (*≡* pq) =
 ⊥.elim {A = λ x → p ≡ q} ((posNotnegsuc 1 0)
 (sym (sign↥p·↧q≡sign↥p p q) ∙ (cong sign pq) ∙ (sign↥p·↧q≡sign↥p q p)))
≃→≡ {p@((negsuc m , n) , c)} {q@((pos zero , n') , c')} (*≡* pq) =
  ⊥.elim {A = λ x → p ≡ q} ((negsucNotpos 0 0)
  (sym (sign↥p·↧q≡sign↥p p q) ∙ (cong sign pq) ∙ (sign↥p·↧q≡sign↥p q p)))
≃→≡ {p@((negsuc m , n) , c)} {q@((pos (suc m') , n') , c')} (*≡* pq) =
  ⊥.elim {A = λ x → p ≡ q} ((negsucNotpos 0 1)
  (sym (sign↥p·↧q≡sign↥p p q) ∙ (cong sign pq) ∙ (sign↥p·↧q≡sign↥p q p)))
≃→≡ {p@((negsuc m , n) , c)} {q@((negsuc m' , n') , c')} (*≡* pq) =
  let npq = (↥p·↧q≡↥q·↧p'→↥↧p≡↥↧qPos {c = c}{c' = c'} (p≃q→-p≃-q {p}{q} pq))
  in ℚ-unique (cong negsuc (injSuc (injPos (cong (λ a → (a .fst)) npq))))
     (cong (λ a → (a .snd)) npq)


-- Equality relation (normalised) and equality
≃≡≡ : ∀ (p q : ℚ) → (p ≃ q) ≡ (p ≡ q)
≃≡≡ p q = isoToPath (iso ≃→≡ ≡→≃ (λ b → isSetℚ p q (≃→≡ (≡→≃ b)) b)
                      (λ a → isProp≃ (≡→≃ (≃→≡ a)) a))

discreteℚ : Discrete ℚ
discreteℚ m n = subst Dec (≃≡≡ m n) dec≃

≡Dec : ∀ (p q : ℚ) → Dec (p ≡ q)
≡Dec p q = discreteℚ p q

refl≃ : ∀ p → p ≃ p
refl≃ p = transport⁻ (≃≡≡ p p) refl

sym≃-≡ : ∀ p q → (p ≃ q) ≡ (q ≃ p)
sym≃-≡ p q = isoToPath
  (iso (λ x → *≡* (sym (*≡*⁻¹ x))) (λ x → *≡* (sym (*≡*⁻¹ x)))
   (λ b → isProp≃
    (*≡* (λ i → *≡*⁻¹ {p}{q} (*≡* (λ i₁ → *≡*⁻¹ b (~ i₁))) (~ i))) b)
   (λ a → isProp≃
    (*≡* (λ i → *≡*⁻¹ {q}{p} (*≡* (λ i₁ → *≡*⁻¹ a (~ i₁))) (~ i))) a))

isEquiv≃ : isEquivRel _≃_
isEquiv≃ = equivRel (λ a → refl≃ a) (λ a b x → transport (sym≃-≡ a b) x)
  λ a b c x y → ≡→≃ ((≃→≡ x) ∙ (≃→≡ y))

sym≃ : ∀{p}{q} → p ≃ q → q ≃ p
sym≃ {p}{q} = isEquiv≃ .symmetric p q

trans≃ : ∀ {p}{q}{r} → p ≃ q → q ≃ r → p ≃ r
trans≃ {p}{q}{r} = isEquiv≃ .transitive p q r

sym≄ : ∀ {m}{n} → (m ≄ n) → (n ≄ m)
sym≄ {m}{n} mn = λ x → mn (sym≃ x)

----------------------------------------------------------
-- Unnormalised equivalence

module gcd-helpers where
  ↥·gcd-pos : ∀ n d1 →
    pos n ≡ (↥ normalise n (1+ d1)) ℤ· ℤ.gcd (pos n) (pos (suc d1))
  ↥·gcd-pos n d1 = sym (let open ToCoprime (n , (1+ d1)) in cong pos p₁) ∙
    (pos·pos (fst (ToCoprime.toCoprime (n , (1+ d1)))) (gcd n (suc d1)))

  ↥·gcd-negsuc : ∀ n d1 → negsuc n ≡
    ↥ (- normalise (suc n) (1+ d1)) ℤ· ℤ.gcd (negsuc n) (pos (suc d1))
  ↥·gcd-negsuc n d1 =
    (cong -ℤ_ (↥·gcd-pos (suc n) d1) ∙
    (-DistL· (↥ normalise (suc n) (1+ d1))
     (ℤ.gcd (pos (suc n)) (pos (suc d1))))) ∙
    (cong₂ (λ a b → a ℤ· b) (sym (↥-neg (normalise (suc n) (1+ d1))))
    (gcd-def (negsuc n) (pos (suc d1)) ∙
     sym (gcd-def (negsuc n) (pos (suc d1)))))

  ↧·gcd-pos : ∀ n d1 → pos (suc d1) ≡
    ↧ normalise n (1+ d1) ℤ· ℤ.gcd (pos n) (pos (suc d1))
  ↧·gcd-pos n d1 = sym (let open ToCoprime (n , (1+ d1)) in cong pos p₂) ∙
    pos·pos (ℕ₊₁→ℕ (ToCoprime.c₂ (n , (1+ d1)))) (gcd n (ℕ₊₁→ℕ (1+ d1))) ∙
    (cong (λ a → a ℤ· ℤ.gcd (pos n) (pos (suc d1))) step)
    where
      step : pos (ℕ₊₁→ℕ (ToCoprime.c₂ (n , (1+ d1)))) ≡ ↧ normalise n (1+ d1)
      step = refl

  ↧·gcd-negsuc : ∀ n d1 →
    pos (suc d1) ≡ ↧ (- normalise (suc n) (1+ d1)) ℤ·
     ℤ.gcd (negsuc n) (pos (suc d1))
  ↧·gcd-negsuc n d1 =
    let open ToCoprime ((suc n) , (1+ d1)) in sym (cong pos p₂) ∙
    pos·pos (ℕ₊₁→ℕ (ToCoprime.c₂ ((suc n) , (1+ d1))))
     (gcd (suc n) (ℕ₊₁→ℕ (1+ d1))) ∙
    cong (λ a → a ℤ· ℤ.gcd (pos (suc n)) (pos (suc d1))) step ∙
    cong (λ a → a ℤ· ℤ.gcd (negsuc n) (pos (suc d1)))
     (sym (↧-neg (normalise (suc n) (1+ d1))))
    where
      step : pos (ℕ₊₁→ℕ (ToCoprime.c₂ ((suc n) , (1+ d1)))) ≡
       ↧ normalise (suc n) (1+ d1)
      step = refl

  ↧₊₁·gcd-pos : ∀ n d-1 →
    1+ d-1 ≡ ↧₊₁ (normalise n (1+ d-1)) ·₊₁ 1+ (predℕ (gcd n (suc d-1)))
  ↧₊₁·gcd-pos n d-1 = ℕ₊₁→ℤ-inj (step1 ∙ step2)
    where
      step1 = ↧·gcd-pos n d-1 ∙ cong (λ u → ↧ normalise n (1+ d-1) ℤ· u)
       (sym (ℕ₊₁→ℤ-gcd-def n d-1))
      step2 = sym (·ℕ₊₁→ℤ-distr (↧₊₁ normalise n (1+ d-1))
       (1+ predℕ (gcd n (suc d-1))))

  ↧₊₁·gcd-negsuc : ∀ n d-1 →
    1+ d-1 ≡ ↧₊₁ (- normalise (suc n) (1+ d-1)) ·₊₁ 1+
     (predℕ (gcd (suc n) (suc d-1)))
  ↧₊₁·gcd-negsuc n d-1 = ℕ₊₁→ℤ-inj (step1 ∙ step2)
    where
      step1 = ↧·gcd-negsuc n d-1 ∙ cong
       (λ u → ℕ₊₁→ℤ (↧₊₁ (- normalise (suc n) (1+ d-1))) ℤ· u)
       (sym (ℕ₊₁→ℤ-gcd-def (suc n) d-1))
      step2 = sym (·ℕ₊₁→ℤ-distr (↧₊₁ (- normalise (suc n) (1+ d-1)))
       (1+ predℕ (gcd (suc n) (suc d-1))))

open gcd-helpers

↥·gcd-lemma : ∀ numerator d-1 -> numerator ≡
  (↥ [ numerator , 1+ d-1 ]) ℤ· (ℤ.gcd numerator (pos (suc d-1)))
↥·gcd-lemma (pos n) d-1 = ↥·gcd-pos n d-1
↥·gcd-lemma (negsuc n) d-1 = ↥·gcd-negsuc n d-1

↧·gcd-lemma : ∀ numerator d-1 -> pos (suc d-1) ≡
  (↧ [ numerator , 1+ d-1 ]) ℤ· (ℤ.gcd numerator (pos (suc d-1)))
↧·gcd-lemma (pos n) d-1 = ↧·gcd-pos n d-1
↧·gcd-lemma (negsuc n) d-1 = ↧·gcd-negsuc n d-1

↧₊₁·gcd-lemma : ∀ numerator d-1 →
  1+ d-1 ≡ (↧₊₁ [ numerator , 1+ d-1 ]) ·₊₁
   (1+ (predℕ (gcd (absℤ numerator) (suc d-1))))
↧₊₁·gcd-lemma (pos n) d-1 = ↧₊₁·gcd-pos n d-1
↧₊₁·gcd-lemma (negsuc n) d-1 = ↧₊₁·gcd-negsuc n d-1

*≃*ᵘ : ∀{x}{y}{d-1}{d-1'} →
  x ℤ· pos (suc d-1') ≡ y ℤ· pos (suc d-1) → [ x , 1+ d-1 ] ≃ [ y , 1+ d-1' ]
*≃*ᵘ {x}{y}{d-1}{d-1'} xy = *≡* res
  where
    lhs = cong₂ (λ x' d-1'' → x' ℤ· d-1'')
     (↥·gcd-lemma x d-1) (↧·gcd-lemma y d-1')
    rhs = cong₂ (λ x' d-1'' → x' ℤ· d-1'')
     (↥·gcd-lemma y d-1') (↧·gcd-lemma x d-1)
    step : ∀ {a}{b}{c}{d}{x}{y} → ¬ (x ≡ 0) → ¬ (y ≡ 0) →
     (a ℤ· x) ℤ· (b ℤ· y) ≡ (c ℤ· y) ℤ· (d ℤ· x) → (a ℤ· b) ≡ (c ℤ· d)
    step {a}{b}{c}{d}{x}{y} nx0 ny0 abcd =
      ·rCancel (x ℤ· y) (a ℤ· b) (c ℤ· d)
       (sym (ab'cd≡ac'bd a x b y) ∙ abcd ∙ (ab'cd≡ac'bd c y d x) ∙
       (cong (λ u → (c ℤ· d) ℤ· u) (·Comm y x))) (¬x≡0¬y≡0→¬x·y≡0 nx0 ny0)
    res : (↥ [ x , (1+ d-1) ]) ℤ· (↧ [ y , (1+ d-1') ]) ≡
          (↥ [ y , (1+ d-1') ]) ℤ· (↧ [ x , (1+ d-1) ])
    res = step
      {↥ [ x , (1+ d-1) ]}{↧ [ y , (1+ d-1') ]}
      {↥ [ y , (1+ d-1') ]}{↧ [ x , (1+ d-1) ]}
      {ℤ.gcd x (pos (suc d-1))}{ℤ.gcd y (pos (suc d-1'))}
      (gcdSucNot0 x d-1) (gcdSucNot0 y d-1') ((sym lhs) ∙ xy ∙ rhs)

*≃*ᵘ⁻¹ : ∀{x}{y}{d-1}{d-1'} → [ x , 1+ d-1 ] ≃ [ y , 1+ d-1' ] →
  x ℤ· pos (suc d-1') ≡ y ℤ· pos (suc d-1)
*≃*ᵘ⁻¹ {x} {y} {d-1} {d-1'} (*≡* xy) = step1 ∙ step2 ∙ step3 ∙ step4
  where
    step1 = sym (abcd≡ac'bd (↥ [ x , (1+ d-1) ]) (↧ [ y , (1+ d-1') ])
      (ℤ.gcd x (pos (suc d-1))) (ℤ.gcd y (pos (suc d-1'))) ∙
      cong₂ (λ a b → a ℤ· b) (sym (↥·gcd-lemma x d-1)) (sym (↧·gcd-lemma y d-1')))
    step2 = cong (λ a → a ℤ· ℤ.gcd x (pos (suc d-1)) ℤ·
      ℤ.gcd y (pos (suc d-1'))) xy
    step3 = (ab'c≡ac'b ((↥ [ y , (1+ d-1') ]) ℤ·
      ((↧ [ x , (1+ d-1) ]))) (ℤ.gcd x (pos (suc d-1))) (ℤ.gcd y (pos (suc d-1'))))
    step4 = abcd≡ac'bd (↥ [ y , (1+ d-1') ]) (↧ [ x , (1+ d-1) ])
      (ℤ.gcd y (pos (suc d-1'))) (ℤ.gcd x (pos (suc d-1))) ∙
      cong₂ (λ a b → a ℤ· b) (sym (↥·gcd-lemma y d-1')) (sym (↧·gcd-lemma x d-1))

*≡*ᵘ : ∀{x}{y}{d-1}{d-1'} →
  x ℤ· pos (suc d-1') ≡ y ℤ· pos (suc d-1) → [ x , 1+ d-1 ] ≡ [ y , 1+ d-1' ]
*≡*ᵘ {x}{y}{d-1}{d-1'} xy = ≃→≡ (*≃*ᵘ {x}{y}{d-1}{d-1'} xy)

*≡*ᵘ⁻¹ : ∀{x}{y}{d-1}{d-1'} → [ x , 1+ d-1 ] ≡ [ y , 1+ d-1' ] →
  x ℤ· pos (suc d-1') ≡ y ℤ· pos (suc d-1)
*≡*ᵘ⁻¹ {x}{y}{d-1}{d-1'} xy = *≃*ᵘ⁻¹ {x}{y}{d-1}{d-1'} (≡→≃ xy)

-- Equality relation (unnormalised) and equality
≃ᵘ≡≡ : ∀ {x}{y}{d-1}{d-1'} →
  (x ℤ.· pos (suc d-1') ≡ y ℤ.· pos (suc d-1)) ≡ ([ x ,  1+ d-1 ] ≡ [ y , 1+ d-1' ])
≃ᵘ≡≡ {x}{y}{d-1}{d-1'} = isoToPath (iso (*≡*ᵘ  {x}{y}{d-1}{d-1'}) (*≡*ᵘ⁻¹ {x}{y}{d-1}{d-1'})
  (λ b → (isSetℚ [ x , (1+ d-1) ] [ y , (1+ d-1') ])
   (*≡*ᵘ {x}{y}{d-1}{d-1'} (*≡*ᵘ⁻¹ {x}{y}{d-1}{d-1'} b)) b)
  (λ a → (ℤ.isSetℤ (x ℤ.· pos (suc d-1')) (y ℤ.· pos (suc d-1)))
   (*≡*ᵘ⁻¹ {x}{y}{d-1}{d-1'} (*≡*ᵘ {x}{y}{d-1}{d-1'} a)) a))

----------------------------------------------------------
-- Type ordering

infix 4 _≤_
_≤_ : ℚ → ℚ → Type
p ≤ q =  (↥ p ℤ.· ↧ q) ℤ.≤ (↥ q ℤ.· ↧ p)

≤Dec : ∀ p q → Dec (p ≤ q)
≤Dec p q = ℤ.≤Dec (↥ p ℤ.· ↧ q) (↥ q ℤ.· ↧ p)

-----------------------------------------------------------
-- Natural number and negative integer literals for ℚ

open import Cubical.Data.Nat.Literals public

instance
  fromNatℚ : HasFromNat ℚ
  fromNatℚ = record { Constraint = λ _ → Unit ;
                      fromNat = λ n → [ pos n , 1 ]}
negDisplay : ℕ → ℚ
negDisplay zero = [ pos 0 , 1 ]
negDisplay (suc n) = [ negsuc n , 1 ]

instance
  fromNegℚ : HasFromNeg ℚ
  fromNegℚ = record { Constraint = λ _ → Unit ;
                      fromNeg = λ n → negDisplay n }

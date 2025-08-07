{-

Base facts about that the ring ℤ is Bézout domain

-}
module Cubical.Data.Int.Fast.Divisibility where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat
  hiding   (+-assoc ; +-comm ; ·-comm)
  renaming (_·_ to _·ℕ_; _+_ to _+ℕ_ ; ·-assoc to ·ℕ-assoc)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Divisibility
  using    (m∣n→m≤n)
  renaming (_∣_ to _∣ℕ_ ; isProp∣ to isProp∣ℕ ; stDivIneq to stDivIneqℕ)
open import Cubical.Data.Nat.Mod
open import Cubical.Data.Int.Base as ℤ
  hiding   (_+_ ; _·_ ; _-_ ; -_)
open import Cubical.Data.Int.Fast.Properties as ℤ
  hiding (addEq ; ·Comm ; ·Assoc ; +Comm ; +Assoc ; ·DistL+)

open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.Relation.Nullary

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Fast.Int
open import Cubical.Tactics.CommRingSolver

private
  variable
    m n k : ℤ


open CommRingStr      (ℤCommRing .snd)

-- The Divisibility Relation
-- Most definitions are the same as in Cubical.Data.Nat.Divisibility

_∣_ : ℤ → ℤ → Type
m ∣ n = ∃[ c ∈ ℤ ] c · m ≡ n

isProp∣ : isProp (m ∣ n)
isProp∣ = squash₁

-- Untruncated divisiblility relation

_∣'_ : ℤ → ℤ → Type
pos 0  ∣' n = 0 ≡ n
pos (suc m) ∣' n = Σ[ c ∈ ℤ ] c · (pos (suc m)) ≡ n
(negsuc m)  ∣' n = Σ[ c ∈ ℤ ] c · (negsuc m)    ≡ n

isProp∣' : isProp (m ∣' n)
isProp∣' {m = pos 0} {n = n} = isSetℤ 0 n
isProp∣' {m = pos (suc m)} {n = n} p q =
  Σ≡Prop (λ _ → isSetℤ _ _) (·rCancel (pos (suc m)) _ _ (p .snd ∙ sym (q .snd)) (λ r → snotz (injPos r)))
isProp∣' {m = negsuc m} {n = n} p q =
  Σ≡Prop (λ _ → isSetℤ _ _) (·rCancel (negsuc m) _ _ (p .snd ∙ sym (q .snd)) (negsucNotpos _ 0))

∣→∣' : (m n : ℤ) → m ∣ n → m ∣' n
∣→∣' (pos 0) n ∣ c , p ∣₁   =  sym (·AnnihilR c) ∙ p
∣→∣' (pos (suc m)) n ∣ p ∣₁ = p
∣→∣' (negsuc m) n ∣ p ∣₁    = p
∣→∣' m n (squash₁ p q i)    = isProp∣' (∣→∣' _ _ p) (∣→∣' _ _ q) i

∣'→∣ : (m n : ℤ) → m ∣' n → m ∣ n
∣'→∣ (pos 0) n p = ∣ 0 , p ∣₁
∣'→∣ (pos (suc m)) n p = ∣ p ∣₁
∣'→∣ (negsuc m) n p = ∣ p ∣₁

∣≃∣' : (m n : ℤ) → (m ∣ n) ≃ (m ∣' n)
∣≃∣' m n = propBiimpl→Equiv isProp∣ isProp∣' (∣→∣' _ _) (∣'→∣ _ _)

-- Properties of divisibility

∣-left : m ∣ (m · k)
∣-left {k = k} = ∣ k , ·Comm k _ ∣₁

∣-right : m ∣ (k · m)
∣-right {k = k} =  ∣ k , refl ∣₁

∣-refl : m ≡ n → m ∣ n
∣-refl p = ∣ 1 ,  ℤ.·IdL _ ∙ p ∣₁

∣-zeroˡ : 0 ∣ m → 0 ≡ m
∣-zeroˡ = ∣→∣' _ _

∣-zeroʳ : m ∣ 0
∣-zeroʳ = ∣ 0 , ·AnnihilL _ ∣₁

∣-+ : k ∣ m → k ∣ n → k ∣ (m + n)
∣-+ =
  Prop.map2
    λ {(c₁ , p) (c₂ , q) → (c₁ + c₂ , ·DistL+ c₁ c₂ _ ∙ (λ t → p t + q t))}

∣-trans : k ∣ m → m ∣ n → k ∣ n
∣-trans =
  Prop.map2
    λ {(c₁ , p) (c₂ , q) → (c₂ · c₁ , sym (·Assoc c₂ c₁ _) ∙ cong (c₂ ·_) p ∙ q)}

∣-left· : k ∣ n → k ∣ (n · m)
∣-left· {k = k} {m = m} p = ∣-trans p (∣-left {k = m})

∣-right· : k ∣ m → k ∣ (n · m)
∣-right· {k = k} {n = n} p = ∣-trans p (∣-right {k = n})


-- Natural numbers back and forth (using abs)

∣→∣ℕ : m ∣ n → abs m ∣ℕ abs n
∣→∣ℕ {m = m} = Prop.rec isProp∣ℕ (λ (c , h) → ∣ abs c , sym (abs· c m) ∙ cong abs h ∣₁)

private
  ∣ℕ→∣-helper : (m n : ℤ)
    → (c : ℕ)(h : c ·ℕ abs m ≡ abs n)
    → (m ≡ pos (abs m)) ⊎ (m ≡ - pos (abs m))
    → (n ≡ pos (abs n)) ⊎ (n ≡ - pos (abs n))
    → Σ[ d ∈ ℤ ] d · m ≡ n
  ∣ℕ→∣-helper _ _ c _ (inl _) (inl _) .fst = pos c
  ∣ℕ→∣-helper m n c h (inl p) (inl q) .snd =
      (λ t → pos c · p t)
    ∙ cong pos h
    ∙ sym q
  ∣ℕ→∣-helper _ _ c _ (inl _) (inr _) .fst = - pos c
  ∣ℕ→∣-helper m n c h (inl p) (inr q) .snd =
      (λ t → - pos c · p t)
    ∙ sym (-DistL· (pos c) (pos (abs m)))
    ∙ (λ t → - pos·pos c (abs m) (~ t))
    ∙ cong (-_) (cong pos h)
    ∙ sym q
  ∣ℕ→∣-helper _ _ c _ (inr _) (inl _) .fst = - pos c
  ∣ℕ→∣-helper m n c h (inr p) (inl q) .snd =
      (λ t → - pos c · p t)
    ∙ sym (-DistLR· (pos c) (pos (abs m)))
    ∙ sym (pos·pos c (abs m))
    ∙ cong pos h
    ∙ sym q
  ∣ℕ→∣-helper _ _ c _ (inr _) (inr _) .fst = pos c
  ∣ℕ→∣-helper m n c h (inr p) (inr q) .snd =
      (λ t → pos c · p t)
    ∙ sym (-DistR· (pos c) (pos (abs m)))
    ∙ (λ t → - pos·pos c (abs m) (~ t))
    ∙ cong (-_) (cong pos h)
    ∙ sym q

∣ℕ→∣ : abs m ∣ℕ abs n → m ∣ n
∣ℕ→∣ = Prop.rec isProp∣ (λ (c , h) → ∣ ∣ℕ→∣-helper _ _ c h (abs→⊎ _ _ refl) (abs→⊎ _ _ refl) ∣₁)

¬∣→¬∣ℕ : ¬ m ∣ n → ¬ abs m ∣ℕ abs n
¬∣→¬∣ℕ p q = p (∣ℕ→∣ q)


-- Inequality for strict divisibility

stDivIneq : ¬ m ≡ 0 → ¬ m ∣ n → k ∣ m → k ∣ n → abs k < abs m
stDivIneq p q h h' = stDivIneqℕ (¬x≡0→¬abs≡0 p) (¬∣→¬∣ℕ q) (∣→∣ℕ h) (∣→∣ℕ h')


-- Exact division

divide : m ∣ n → ℤ
divide {m = pos 0} _ = 0
divide {m = pos (suc m)} p = ∣→∣' _ _ p .fst
divide {m = negsuc m} p = ∣→∣' _ _ p .fst

divideEq : (p : m ∣ n) → divide p · m ≡ n
divideEq {m = pos 0} = ∣→∣' _ _
divideEq {m = pos (suc m)} p = ∣→∣' _ _ p .snd
divideEq {m = negsuc m} p = ∣→∣' _ _ p .snd


-- Bézout and Euclidean Domain

record Bézout (m n : ℤ) : Type where
  constructor bezout
  field
    coef₁ : ℤ
    coef₂ : ℤ
    gcd   : ℤ
    identity : coef₁ · m + coef₂ · n ≡ gcd
    isCD  : (gcd ∣ m) × (gcd ∣ n)

open Bézout

Bézout0 : (n : ℤ) → Bézout 0 n
Bézout0 n .coef₁ = 0
Bézout0 n .coef₂ = 1
Bézout0 n .gcd   = n
Bézout0 n .identity = ℤ.+IdL _ ∙ ℤ.·IdL n
Bézout0 n .isCD  = ∣-zeroʳ , ∣-refl refl

bézoutReduction : (m d r : ℤ) → Bézout r m → Bézout m (d · m + r)
bézoutReduction m d r b .coef₁ = - b .coef₁ · d + b .coef₂
bézoutReduction m d r b .coef₂ = b .coef₁
bézoutReduction m d r b .gcd   = b .gcd
bézoutReduction m d r b .identity =
   solve! ℤCommRing ∙ b .identity
bézoutReduction m d r b .isCD .fst = b .isCD .snd
bézoutReduction m d r b .isCD .snd = ∣-+ (∣-right· {n = d} (b .isCD .snd)) (b .isCD .fst)

-- Properties of Bézout identity

module _
  (b : Bézout m n) where

  private
    g = b .gcd

  gcdIsGCD : k ∣ m → k ∣ n → k ∣ g
  gcdIsGCD {k = k} p q =
    subst (k ∣_) (b .identity) (∣-+ (∣-right· {n = b .coef₁} p) (∣-right· {n = b .coef₂} q))

  gcd≡0 : g ≡ 0 → (m ≡ 0) × (n ≡ 0)
  gcd≡0 p .fst = sym (∣-zeroˡ (subst (λ a → a ∣ _) p (b .isCD .fst)))
  gcd≡0 p .snd = sym (∣-zeroˡ (subst (λ a → a ∣ _) p (b .isCD .snd)))

  ¬m≡0→¬gcd≡0 : ¬ m ≡ 0 → ¬ g ≡ 0
  ¬m≡0→¬gcd≡0 p q = p (gcd≡0 q .fst)

  div₁ div₂ : ℤ
  div₁ = divide (b .isCD .fst)
  div₂ = divide (b .isCD .snd)

  div·-helper : g · (div₁ · n) ≡ g · (div₂ · m)
  div·-helper =
      ·Assoc g div₁ n
    ∙ (λ i → ·Comm g div₁ i · n)
    ∙ (λ i → divideEq (b .isCD .fst) i · n)
    ∙ ·Comm m n
    ∙ (λ i → divideEq (b .isCD .snd) (~ i) · m)
    ∙ (λ i → ·Comm div₂ g i · m)
    ∙ sym (·Assoc g div₂ m)

  div·-g≠0 : ¬ g ≡ 0 → div₁ · n ≡ div₂ · m
  div·-g≠0 p = ·lCancel _ _ _ div·-helper p

  div·-g≡0 : g ≡ 0 → div₁ · n ≡ div₂ · m
  div·-g≡0 p =
      (λ i → div₁ · gcd≡0 p .snd i)
    ∙ ·AnnihilR div₁
    ∙ sym (·AnnihilR div₂)
    ∙ λ i → div₂ · gcd≡0 p .fst (~ i)

  div·-case : Dec (g ≡ 0) → div₁ · n ≡ div₂ · m
  div·-case (yes p) = div·-g≡0  p
  div·-case (no ¬p) = div·-g≠0 ¬p

  div· : div₁ · n ≡ div₂ · m
  div· = div·-case (discreteℤ g 0)

  div·- : - div₂ · m + div₁ · n ≡ 0
  div·- =  (λ i → -DistL· div₂ m (~ i) + div₁ · n)
          ∙ subst (λ a → - a + div₁ · n ≡ 0) div· (-Cancel' (div₁ · n))

-- Quotient and Remainder

record QuotRem (m n : ℤ) : Type where
  constructor quotrem
  field
    div : ℤ
    rem : ℤ
    quotEq : n ≡ div · m + rem
    normIneq : (rem ≡ 0) ⊎ ((¬ rem ≡ 0) × (abs rem < abs m))

open QuotRem

-- Using remainder to decide divisibility

module _
  (m n : ℤ)(qr : QuotRem m n) where

  rem≡0→m∣n : qr .rem ≡ 0 → m ∣ n
  rem≡0→m∣n p = ∣ qr .div ,  sym (ℤ.+IdR _) ∙∙ cong (qr .div · m +_) (sym p) ∙∙ sym (qr .quotEq) ∣₁

  m∣n→rem≡0 : m ∣ n → qr .rem ≡ 0
  m∣n→rem≡0 p =
    case qr .normIneq
    return _ of λ
    { (inl q) → q
    ; (inr q) →
        let ∣+  = ∣-+ p (∣-right {m = m} {k = - qr .div})
            m∣r = subst {x = n + - qr .div · m} {y = qr .rem}
                (m ∣_) (cong (_+ _) (qr .quotEq) ∙ solve! ℤCommRing) ∣+
            m≤r = m∣n→m≤n (¬x≡0→¬abs≡0 (q .fst)) (∣→∣ℕ m∣r)
        in  Empty.rec (<-asym (q .snd) m≤r) }

  m∣n→rem≡0' : (p : m ∣ n) → qr .normIneq ≡ inl (m∣n→rem≡0 p)
  m∣n→rem≡0' p =
    case (qr .normIneq)
    return (λ x → x ≡ inl (m∣n→rem≡0 p)) of λ
    { (inl q) → cong inl (isSet→SquareP (λ i j → isSetℤ) q (m∣n→rem≡0 p) refl refl)
    ; (inr q) → Empty.rec (q .fst (m∣n→rem≡0 p)) }

  rem≢0→m∤n : ¬ qr .rem ≡ 0 → ¬ m ∣ n
  rem≢0→m∤n p q = p (m∣n→rem≡0 q)

-- The Euclidean Algorithm
module _
  (decEq0  : (n : ℤ) → Dec (n ≡ 0))
  (quotRem : (m n : ℤ)(¬z : ¬ m ≡ 0) → QuotRem m n) where

  euclidStep : (norm : ℕ)
    → (m n : ℤ)(h : abs m < norm)
    → (b : QuotRem m n)
    → Bézout m n
  euclidStep 0 _ _ h _ = Empty.rec (¬-<-zero h)
  euclidStep (suc N) m n h (quotrem div rem quotEq (inl p)) =
    let q = subst (λ r → n ≡ div · m + r) p quotEq
    in  bezout 1 0 m (
      1 · m + 0 · n ≡⟨ cong (1 · m +_) (·AnnihilL n) ⟩
      1 · m + 0     ≡⟨ ℤ.+IdR (1 · m) ⟩
      1 · m         ≡⟨ ℤ.·IdL m ⟩
      m             ∎ )
      (∣-refl refl , subst (λ k → m ∣ k) (sym q) (subst (m ∣_) (sym (ℤ.+IdR (div · m))) (∣-right {k = div})) )
  euclidStep (suc N) m n h (quotrem div rem quotEq (inr p)) =
    let b = euclidStep N rem m (<≤-trans (p .snd) (pred-≤-pred h)) (quotRem _ _ (p .fst))
    in  subst (λ x → Bézout m x) (sym quotEq) (bézoutReduction _ div _ b)

  private
    euclid-helper : (m n : ℤ)(dec : Dec (m ≡ 0)) → Bézout m n
    euclid-helper m n (yes z) = subst (λ x → Bézout x n) (sym z) (Bézout0 n)
    euclid-helper m n (no ¬z) = euclidStep (suc (abs m)) m n ≤-refl (quotRem m n ¬z)

  euclid : (m n : ℤ) → Bézout m n
  euclid m n = euclid-helper m n (decEq0 _)

  -- Euclid algorithm when divisibility holds
  euclid∣ : (m n : ℤ) → ¬ m ≡ 0 → m ∣ n → (euclid m n .coef₁ ≡ 1) × (euclid m n .coef₂ ≡ 0)
  euclid∣ _ _ = euclid∣-helper _ _ (decEq0 _)
    where
    euclid∣-helper : (m n : ℤ)(dec : Dec (m ≡ 0)) → ¬ m ≡ 0 → m ∣ n
      → (euclid-helper m n dec .coef₁ ≡ 1) × (euclid-helper m n dec .coef₂ ≡ 0)
    euclid∣-helper _ _ (yes z) q = Empty.rec (q z)
    euclid∣-helper m n (no ¬z) _ q =
      let qr = quotRem m n ¬z
          path : qr ≡ quotrem _ _ _ _
          path t = record qr { normIneq = m∣n→rem≡0' _ _ qr q t }
      in  (λ t → euclidStep (suc (abs m)) m n ≤-refl (path t) .coef₁) ,
          (λ t → euclidStep (suc (abs m)) m n ≤-refl (path t) .coef₂)


-- The ring ℤ is an Euclidean domain

private
  dec-helper : {ℓ ℓ' : Level}{A : Type ℓ}{B : Type ℓ'} → Dec A → B → A ⊎ ((¬ A) × B)
  dec-helper (yes p) _ = inl p
  dec-helper (no ¬p) b = inr (¬p , b)

quotRemPosPos : (m n : ℕ)(¬z : ¬ pos m ≡ 0) → QuotRem (pos m) (pos n)
quotRemPosPos m n _ .div = pos (quotient  n / m)
quotRemPosPos m n _ .rem = pos (remainder n / m)
quotRemPosPos m n _ .quotEq =
    (λ t → pos (≡remainder+quotient m n (~ t)))
  ∙ pos+ (remainder n / m) (m ·ℕ (quotient n / m))
  ∙ +Comm (pos (remainder n / m)) (pos (m ·ℕ (quotient n / m)))
  ∙ (λ t → pos·pos m (quotient n / m) t + pos (remainder n / m))
  ∙ (λ t → ·Comm (pos m) (pos (quotient n / m)) t + pos (remainder n / m))
quotRemPosPos 0       n ¬z .normIneq = Empty.rec (¬z refl)
quotRemPosPos (suc m) n ¬z .normIneq = dec-helper (discreteℤ _ 0) (mod< m n)

quotRemNegPos : (m n : ℕ)(¬z : ¬ - pos m ≡ 0) → QuotRem (- pos m) (pos n)
quotRemNegPos m n ¬z .div = - (quotRemPosPos m n (λ p → ¬z (λ t → - p t)) .div)
quotRemNegPos m n ¬z .rem = quotRemPosPos m n (λ p → ¬z (λ t → - p t)) .rem
quotRemNegPos m n ¬z .quotEq =
    quotRemPosPos m n (λ p → ¬z (λ t → - p t)) .quotEq
  ∙ (λ t → -DistLR· (pos (quotient n / m)) (pos m) t + (pos (remainder n / m)))
quotRemNegPos 0       n ¬z .normIneq = Empty.rec (¬z refl)
quotRemNegPos (suc m) n ¬z .normIneq = quotRemPosPos (suc m) n (λ p → ¬z (λ t → - p t)) .normIneq

private
  quotRemPos-helper : (m : ℤ)(k n : ℕ)(¬z : ¬ m ≡ 0) → (m ≡ pos k) ⊎ (m ≡ - pos k) → QuotRem m (pos n)
  quotRemPos-helper m k n ¬z (inl p) =
    subst (λ l → QuotRem l (pos n)) (sym p) (quotRemPosPos k n (λ r → ¬z (p ∙ r)))
  quotRemPos-helper m k n ¬z (inr p) =
    subst (λ l → QuotRem l (pos n)) (sym p) (quotRemNegPos k n (λ r → ¬z (p ∙ r)))

quotRemPos : (m : ℤ)(n : ℕ)(¬z : ¬ m ≡ 0) → QuotRem m (pos n)
quotRemPos m n ¬z = quotRemPos-helper m (abs m) n ¬z (abs→⊎ _ _ refl)

private
  sum-helper : (m r : ℤ)
    → (r ≡ 0)   ⊎ ((¬ r ≡ 0)   × (abs r < abs m))
    → (- r ≡ 0) ⊎ ((¬ - r ≡ 0) × (abs (- r) < abs m))
  sum-helper m r (inl p) = inl (λ t → - p t)
  sum-helper m r (inr p) =
    inr ((λ q → p .fst (sym (-Involutive r) ∙ (λ t → - q t)))
      , subst (λ k → k < abs m) (sym (abs- r)) (p .snd))

quotRemNeg : (m : ℤ)(n : ℕ)(¬z : ¬ m ≡ 0) → QuotRem m (- pos n)
quotRemNeg m n ¬z .div = - (quotRemPos m n ¬z .div)
quotRemNeg m n ¬z .rem = - (quotRemPos m n ¬z .rem)
quotRemNeg m n ¬z .quotEq =
    (λ t → - quotRemPos m n ¬z .quotEq t)
  ∙ -Dist+ (quotRemPos m n ¬z .div · m) (quotRemPos m n ¬z .rem)
  ∙ (λ t → -DistL· (quotRemPos m n ¬z .div) m t + - quotRemPos m n ¬z .rem)
quotRemNeg m n ¬z .normIneq = sum-helper m _ (quotRemPos m n ¬z .normIneq)

private
  quotRem-helper : (m n : ℤ)(k : ℕ)(¬z : ¬ m ≡ 0) → (n ≡ pos k) ⊎ (n ≡ - pos k) → QuotRem m n
  quotRem-helper m n k ¬z (inl p) = subst (λ l → QuotRem m l) (sym p) (quotRemPos m k ¬z)
  quotRem-helper m n k ¬z (inr p) = subst (λ l → QuotRem m l) (sym p) (quotRemNeg m k ¬z)


-- The quotient-remainder Theorem and the Bézout identity

quotRem : (m n : ℤ)(¬z : ¬ m ≡ 0) → QuotRem m n
quotRem m n ¬z = quotRem-helper m n (abs n) ¬z (abs→⊎ _ _ refl)

bézout : (m n : ℤ) → Bézout m n
bézout = euclid (λ m → discreteℤ m 0) quotRem

bézout∣ : (m n : ℤ) → ¬ m ≡ 0 → m ∣ n → (bézout m n .coef₁ ≡ 1) × (bézout m n .coef₂ ≡ 0)
bézout∣ = euclid∣ (λ m → discreteℤ m 0) quotRem


-- Divisibility is decidable
dec∣ : (m n : ℤ) → Dec (m ∣ n)
dec∣ m n =
  case discreteℤ m 0
  return (λ _ → Dec (m ∣ n)) of λ
  { (yes p) →
      case discreteℤ n 0
      return (λ _ → Dec (m ∣ n)) of λ
      { (yes p) → yes (subst (m ∣_) (sym p) ∣-zeroʳ)
      ; (no ¬p) → no  (λ r → ¬p (sym (∣-zeroˡ (subst (_∣ n) p r)))) }
  ; (no ¬p) →
      let qr = quotRem m n ¬p in
      case discreteℤ (qr .rem) 0
      return (λ _ → Dec (m ∣ n)) of λ
      { (yes p) → yes (rem≡0→m∣n _ _ qr  p)
      ; (no ¬p) → no  (rem≢0→m∤n _ _ qr ¬p) }}

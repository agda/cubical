module Cubical.Data.Nat.GCD where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

open import Cubical.Induction.WellFounded

open import Cubical.Data.Sigma as Σ
open import Cubical.Data.Sum
open import Cubical.Data.Fin as F hiding (_%_ ; _/_)

open import Cubical.HITs.PropositionalTruncation as PropTrunc

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat.Base
open import Cubical.Data.Nat.Properties
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Order.Inductive
open import Cubical.Data.Nat.Mod renaming (
  quotient_/_  to _/_ ; remainder_/_ to _%_
  ; ≡remainder+quotient to ≡%+·/ ; mod< to %< )
open import Cubical.Data.Nat.Divisibility

open import Cubical.Data.Int.Base as ℤ using (ℤ ; pos ; negsuc ; abs) renaming (_·_ to _ℤ·_; _+_ to _ℤ+_ ; -_ to -ℤ_)
open import Cubical.Data.Int.Properties as ℤ using (injPos; injNegsuc; pos·pos; pos0+; -Dist+; -DistL·; negsucNotpos; negsuc·possuc;  pos+;  +CancelRNegsuc; negsuc+negsuc-def)
open import Cubical.Data.Int.Order as ℤ using (zero-<sucPos; ≤-+-<; m≤n→posm≤posn)
open import Cubical.Data.Int.Divisibility as ℤ using ()

open import Cubical.Relation.Nullary

private
  variable
    m n c d : ℕ

-- common divisors

isCD : ℕ → ℕ → ℕ → Type₀
isCD m n d = (d ∣ m) × (d ∣ n)

isPropIsCD : isProp (isCD m n d)
isPropIsCD = isProp× isProp∣ isProp∣

symCD : isCD m n d → isCD n m d
symCD (d∣m , d∣n) = (d∣n , d∣m)

-- greatest common divisors

isGCD : ℕ → ℕ → ℕ → Type₀
isGCD m n d = (isCD m n d) × (∀ d' → isCD m n d' → d' ∣ d)

GCD : ℕ → ℕ → Type₀
GCD m n = Σ ℕ (isGCD m n)

isPropIsGCD : isProp (isGCD m n d)
isPropIsGCD = isProp× isPropIsCD (isPropΠ2 (λ _ _ → isProp∣))

isPropGCD : isProp (GCD m n)
isPropGCD (d , dCD , gr) (d' , d'CD , gr') =
  Σ≡Prop (λ _ → isPropIsGCD) (antisym∣ (gr' d dCD) (gr d' d'CD))

symGCD : isGCD m n d → isGCD n m d
symGCD (dCD , gr) = symCD dCD , λ { d' d'CD → gr d' (symCD d'CD) }

divsGCD : m ∣ n → isGCD m n m
divsGCD p = (∣-refl refl , p) , λ { d (d∣m , _) → d∣m }

divsGCD-inv : ∀ {m}{n} → isGCD m n m → m ∣ n
divsGCD-inv p = p .fst .snd

oneGCD : ∀ m → isGCD m 1 1
oneGCD m = symGCD (divsGCD (∣-oneˡ m))

-- The base case of the Euclidean algorithm
zeroGCD : ∀ m → isGCD m 0 m
zeroGCD m = divsGCD (∣-zeroʳ m)

-- zeroGCD-unique lemma: if d is gcd of m and 0, then d ≡ m
zeroGCD-unique : {m d : ℕ} → isGCD m 0 d → m ≡ d
zeroGCD-unique {m} {d} (iscd , greatest) =
  let
    d∣m = fst iscd
    m∣m = ∣-refl (refl {x = m})
    m∣0 = ∣-zeroʳ m
    m∣d = greatest m (m∣m , m∣0)
  in
  antisym∣ m∣d d∣m

-- a pair of useful lemmas about ∣ and (efficient) %
private
  ∣→∣% : ∀ {m n d} → d ∣ m → d ∣ n → d ∣ (m % n)
  ∣%→∣ : ∀ {m n d} → d ∣ (m % n) → d ∣ n → d ∣ m

∣→∣% {m} {0}         {d} d∣m d∣n = d∣m
∣→∣% {m} {n@(suc _)} {d} d∣m d∣n =
  let
    k₁     = ∣-untrunc d∣m .fst
    k₁·d≡m = ∣-untrunc d∣m .snd
    k₂     = ∣-untrunc d∣n .fst
    k₂·d≡n = ∣-untrunc d∣n .snd
    p      =
      (k₁ ∸ m / n · k₂) · d         ≡⟨ ∸-distribʳ k₁ (m / n · k₂) d ⟩
      k₁ · d ∸ m / n · k₂ · d       ≡⟨ sym $ cong (k₁ · d ∸_) (·-assoc (m / n) _ _) ⟩
      k₁ · d ∸ m / n · (k₂ · d)     ≡⟨ cong₂ (λ l r → l ∸ m / n · r) k₁·d≡m k₂·d≡n ⟩
      m ∸ m / n · n                 ≡⟨ cong (m ∸_) (·-comm (m / n) n) ⟩
      m ∸ n · m / n                 ≡⟨ sym $ cong (_∸ n · m / n) (≡%+·/ n m)  ⟩
      m % n + n · m / n ∸ n · m / n ≡⟨ +∸ (m % n) (n · m / n) ⟩
      m % n                         ∎
  in
    ∣ k₁ ∸ m / n · k₂ , p ∣₁

∣%→∣ {m} {0}         {d} d∣m%n d∣n = d∣m%n
∣%→∣ {m} {n@(suc _)} {d} d∣m%n d∣n =
  let
    k₁       = ∣-untrunc d∣m%n .fst
    k₁·d≡m%n = ∣-untrunc d∣m%n .snd
    k₂       = ∣-untrunc d∣n   .fst
    k₂·d≡n   = ∣-untrunc d∣n   .snd
    p        =
      (k₁ + k₂ · m / n) · d     ≡⟨ sym $ ·-distribʳ k₁ (k₂ · m / n) d ⟩
      k₁ · d + k₂ · m / n · d   ≡⟨ cong (λ p → k₁ · d + p · d) (·-comm k₂ (m / n)) ⟩
      k₁ · d + m / n · k₂ · d   ≡⟨ sym $ cong (k₁ · d +_) (·-assoc (m / n) k₂ d) ⟩
      k₁ · d + m / n · (k₂ · d) ≡⟨ cong₂ (λ l r → l + m / n · r) k₁·d≡m%n k₂·d≡n ⟩
      m % n + m / n · n         ≡⟨ cong (m % n +_) (·-comm (m / n) n) ⟩
      m % n + n · m / n         ≡⟨ ≡%+·/ n m ⟩
      m                         ∎
  in
    ∣ k₁ + k₂ · m / n , p ∣₁

-- The inductive step of the Euclidean algorithm
stepGCD : isGCD (suc n) (m % suc n) d
        → isGCD m       (suc n)     d
stepGCD w =
  let
    g∣1+n            = w .fst .fst
    g∣m%1+n          = w .fst .snd
    d∣1+n→d∣m%1+n→d∣g = w .snd
  in
    (∣%→∣ g∣m%1+n g∣1+n , g∣1+n) ,
    λ d' (d'∣m , d'∣1+n) → d∣1+n→d∣m%1+n→d∣g d' (d'∣1+n , (∣→∣% d'∣m d'∣1+n))

-- putting it all together using an auxiliary variable to pass the termination checking

private
  euclid-helper< : (m n f : ℕ) → (n < m) → (m ≤ f) → GCD m n
  euclid-helper< m       n       zero    n<m m≤0 .fst = 0
  euclid-helper< m       n       zero    n<m m≤0 .snd .fst .fst = ∣-refl $ sym $ ≤0→≡0 m≤0
  euclid-helper< m       n       zero    n<m m≤0 .snd .fst .snd = ∣-refl $ sym $ ≤0→≡0 $
                                                              <-weaken $ <≤-trans n<m m≤0
  euclid-helper< m       n       zero    n<m m≤0 .snd .snd d' _ = ∣-zeroʳ d'
  euclid-helper< zero    zero    (suc _) _   _   .fst = 0
  euclid-helper< zero    zero    (suc _) _   _   .snd .fst .fst = ∣-refl refl
  euclid-helper< zero    zero    (suc _) _   _   .snd .fst .snd = ∣-refl refl
  euclid-helper< zero    zero    (suc _) _   _   .snd .snd d' _ = ∣-zeroʳ d'
  euclid-helper< zero    (suc n) (suc _) _   _   .fst = suc n
  euclid-helper< zero    (suc n) (suc _) _   _   .snd .fst .fst = ∣-zeroʳ (suc n)
  euclid-helper< zero    (suc n) (suc _) _   _   .snd .fst .snd = ∣-refl refl
  euclid-helper< zero    (suc n) (suc _) _   _   .snd .snd d' (_ , d'∣1+n) = d'∣1+n
  euclid-helper< (suc m) zero    (suc _) _   _   .fst = suc m
  euclid-helper< (suc m) zero    (suc _) _   _   .snd .fst .fst = ∣-refl refl
  euclid-helper< (suc m) zero    (suc _) _   _   .snd .fst .snd = ∣-zeroʳ (suc m)
  euclid-helper< (suc m) zero    (suc _) _   _   .snd .snd d' (d'∣1+m , _) = d'∣1+m
  euclid-helper< m@(suc _) n@(suc n-1) (suc f) n<m m≤1+f =
    let
      n≤f = predℕ-≤-predℕ $ <≤-trans n<m m≤1+f
      r   = euclid-helper< n (m % n) f (%< n-1 m) n≤f
    in
      r .fst , stepGCD (r .snd)

euclid : ∀ m n → GCD m n
euclid m zero        = m , (∣-refl refl , ∣-zeroʳ m) , λ d' (d'∣m , _) → d'∣m
euclid m n@(suc n-1) =
  let
    r = euclid-helper< n (m % n) n (%< n-1 m) ≤-refl
  in
    r .fst , stepGCD (r .snd)

isContrGCD : ∀ m n → isContr (GCD m n)
isContrGCD m n = euclid m n , isPropGCD _

-- the gcd operator on ℕ

gcd : ℕ → ℕ → ℕ
gcd m n = euclid m n .fst

gcdIsGCD : ∀ m n → isGCD m n (gcd m n)
gcdIsGCD m n = euclid m n .snd

isGCD→gcd≡ : isGCD m n d → gcd m n ≡ d
isGCD→gcd≡ dGCD = cong fst (isContrGCD _ _ .snd (_ , dGCD))

gcd≡→isGCD : gcd m n ≡ d → isGCD m n d
gcd≡→isGCD p = subst (isGCD _ _) p (gcdIsGCD _ _)

gcd≡isGCD : ∀ m n d → (gcd m n ≡ d) ≡ (isGCD m n d)
gcd≡isGCD m n d = isoToPath (iso gcd≡→isGCD isGCD→gcd≡
  (λ b → isPropIsGCD (gcd≡→isGCD (isGCD→gcd≡ b)) b)
  (λ a →  isSetℕ (gcd m n) d (isGCD→gcd≡ {m}{n}{d} (gcd≡→isGCD a)) a))

uniqueGCD : ∀ {d'} → isGCD m n d → isGCD m n d' → d ≡ d'
uniqueGCD isgd isgd' = sym (isGCD→gcd≡ isgd) ∙ isGCD→gcd≡ isgd'

gcdSym : (m n : ℕ) → (gcd m n) ≡ (gcd n m)
gcdSym m n =  uniqueGCD (gcdIsGCD m n) (symGCD (gcdIsGCD n m))

-- multiplicative properties of the gcd

isCD-cancelʳ : ∀ k → isCD (m · suc k) (n · suc k) (d · suc k)
                   → isCD m n d
isCD-cancelʳ k (dk∣mk , dk∣nk) = (∣-cancelʳ k dk∣mk , ∣-cancelʳ k dk∣nk)

isCD-multʳ : ∀ k → isCD m n d
                 → isCD (m · k) (n · k) (d · k)
isCD-multʳ k (d∣m , d∣n) = (∣-multʳ k d∣m , ∣-multʳ k d∣n)

isGCD-cancelʳ : ∀ k → isGCD (m · suc k) (n · suc k) (d · suc k)
                    → isGCD m n d
isGCD-cancelʳ {m} {n} {d} k (dCD , gr) =
  isCD-cancelʳ k dCD ,  λ d' d'CD → ∣-cancelʳ k (gr (d' · suc k) (isCD-multʳ (suc k) d'CD))

gcd-factorʳ : ∀ m n k → gcd (m · k) (n · k) ≡ gcd m n · k
gcd-factorʳ m n zero = (λ i → gcd (0≡m·0 m (~ i)) (0≡m·0 n (~ i))) ∙ 0≡m·0 (gcd m n)
gcd-factorʳ m n (suc k) = sym p ∙ cong (_· suc k) (sym q)
  where k∣gcd : suc k ∣ gcd (m · suc k) (n · suc k)
        k∣gcd = gcdIsGCD (m · suc k) (n · suc k) .snd (suc k) (∣-right m , ∣-right n)
        d' = ∣-untrunc k∣gcd .fst
        p : d' · suc k ≡ gcd (m · suc k) (n · suc k)
        p = ∣-untrunc k∣gcd .snd

        d'GCD : isGCD m n d'
        d'GCD = isGCD-cancelʳ _ (subst (isGCD _ _) (sym p) (gcdIsGCD (m · suc k) (n · suc k)))
        q : gcd m n ≡ d'
        q = isGCD→gcd≡ d'GCD

-- Q: Can this be proved directly? (i.e. without a transport)
isGCD-multʳ : ∀ k → isGCD m n d
                  → isGCD (m · k) (n · k) (d · k)
isGCD-multʳ {m} {n} {d} k dGCD = gcd≡→isGCD (gcd-factorʳ m n k ∙ cong (_· k) r)
  where r : gcd m n ≡ d
        r = isGCD→gcd≡ dGCD

-- Core properties of gcd

gcd[m,n]∣m : (m n : ℕ) → (gcd m n) ∣ m
gcd[m,n]∣m m n = fst (fst (gcdIsGCD m n))

gcd[m,n]∣n : (m n : ℕ) → (gcd m n) ∣ n
gcd[m,n]∣n m n = transport (cong (λ a → a ∣ n) (gcdSym n m) ) (gcd[m,n]∣m n m)

gcd-greatest : c ∣ m → c ∣ n → c ∣ gcd m n
gcd-greatest = curry (snd (gcdIsGCD _ _) _)

-- Other properties

gcd[0,0]≡0 : gcd 0 0 ≡ 0
gcd[0,0]≡0 = antisym∣ (∣-zeroʳ (gcd 0 0) ) (gcd-greatest (∣-zeroʳ 0) (∣-zeroʳ 0))

gcd[m,n]≢0 : ∀ (m n : ℕ) → (¬ (m ≡ 0)) ⊎ (¬ (n ≡ 0)) → ¬ (gcd m n ≡ 0)
gcd[m,n]≢0 m n (inl m≢0) gcd0 =
  m≢0 (sym (∣-zeroˡ (transport (cong (λ a → a ∣ m) gcd0) (gcd[m,n]∣m m n))))
gcd[m,n]≢0 m n (inr n≢0) gcd0 =
  n≢0 (sym (∣-zeroˡ (transport ((cong (λ a → a ∣ n) gcd0)) (gcd[m,n]∣n m n))))

gcd[m,n]≡0⇒m≡0 : gcd m n ≡ 0 → m ≡ 0
gcd[m,n]≡0⇒m≡0 {zero} {n} gmn = refl
gcd[m,n]≡0⇒m≡0 {suc m} {n} gmn =
  ⊥.elim {A = λ bot → suc m ≡ 0} (gcd[m,n]≢0 (suc m) n (inl snotz) gmn)

gcd[m,n]≡0⇒n≡0 : ∀ {m n} → gcd m n ≡ 0 → n ≡ 0
gcd[m,n]≡0⇒n≡0 {m}{n} gmn = gcd[m,n]≡0⇒m≡0 {n} {m} (gcdSym n m ∙ gmn)

decGCD : ∀ {m}{n}{d} → Dec (isGCD m n d)
decGCD {m}{n}{d} with (discreteℕ (gcd m n) d)
... | yes p = yes (gcd≡→isGCD p)
... | no ¬p = no λ x → ¬p (isGCD→gcd≡ x)

dec∣ : ∀ (m n : ℕ) → Dec (m ∣ n)
dec∣ m n with decGCD {m}{n}{m}
... | yes p = yes (p .fst .snd)
... | no ¬p = no (λ x → ¬p (divsGCD x))

-- Inequality for strict divisibility

stDivIneqGCD : ¬ m ≡ 0 → ¬ m ∣ n → (g : GCD m n) → g .fst < m
stDivIneqGCD p q g = stDivIneq p q (g .snd .fst .fst) (g .snd .fst .snd)

-- Alternative definition of GCD using % from Cubical.Data.Fin and well-founded induction

private
  lem₁ : prediv d (suc n) → prediv d (m F.% suc n) → prediv d m
  lem₁ {d} {n} {m} (c₁ , p₁) (c₂ , p₂) = (q · c₁ + c₂) , p
    where r = m F.% suc n; q = n%k≡n[modk] m (suc n) .fst
          p = (q · c₁ + c₂) · d     ≡⟨ sym (·-distribʳ (q · c₁) c₂ d) ⟩
              (q · c₁) · d + c₂ · d ≡⟨ cong (_+ c₂ · d) (sym (·-assoc q c₁ d))  ⟩
              q · (c₁ · d) + c₂ · d ≡[ i ]⟨ q · (p₁ i) + (p₂ i) ⟩
              q · (suc n)  + r      ≡⟨ n%k≡n[modk] m (suc n) .snd ⟩
              m                     ∎

  lem₂ : prediv d (suc n) → prediv d m → prediv d (m F.% suc n)
  lem₂ {d} {n} {m} (c₁ , p₁) (c₂ , p₂) = c₂ ∸ q · c₁ , p
    where r = m F.% suc n; q = n%k≡n[modk] m (suc n) .fst
          p = (c₂ ∸ q · c₁) · d               ≡⟨ ∸-distribʳ c₂ (q · c₁) d ⟩
              c₂ · d ∸ (q · c₁) · d           ≡⟨ cong (c₂ · d ∸_) (sym (·-assoc q c₁ d)) ⟩
              c₂ · d ∸ q · (c₁ · d)           ≡[ i ]⟨ p₂ i ∸ q · (p₁ i) ⟩
              m      ∸ q · (suc n)            ≡⟨ cong (_∸ q · (suc n)) (sym (n%k≡n[modk] m (suc n) .snd)) ⟩
              (q · (suc n) + r) ∸ q · (suc n) ≡⟨ cong (_∸ q · (suc n)) (+-comm (q · (suc n)) r) ⟩
              (r + q · (suc n)) ∸ q · (suc n) ≡⟨ ∸-cancelʳ r zero (q · (suc n)) ⟩
              r ∎

-- The inductive step of the Euclidean algorithm
stepGCD' : isGCD (suc n) (m F.% suc n) d
        → isGCD m       (suc n)     d
fst (stepGCD' ((d∣n , d∣m%n) , gr)) = PropTrunc.map2 lem₁ d∣n d∣m%n , d∣n
snd (stepGCD' ((d∣n , d∣m%n) , gr)) d' (d'∣m , d'∣n) = gr d' (d'∣n , PropTrunc.map2 lem₂ d'∣n d'∣m)

-- putting it all together using well-founded induction

euclidᵗ : ∀ m n → n <ᵗ m → GCD m n
euclidᵗ = WFI.induction <ᵗ-wellfounded λ {
  m rec zero    p → m , zeroGCD m ;
  m rec (suc n) p → let d , dGCD = rec (suc n) p (m F.% suc n) (n%sk<ᵗsk m n)
                     in d , stepGCD' dGCD }

euclid'< : ∀ m n → n < m → GCD m n
euclid'< m n p = euclidᵗ m n (<→<ᵗ p)

euclid' : ∀ m n → GCD m n
euclid' m n with n ≟ m
... | lt p = euclid'< m n p
... | gt p = Σ.map-snd symGCD (euclid'< n m p)
... | eq p = m , divsGCD (∣-refl (sym p))

gcd' : ℕ → ℕ → ℕ
gcd' m n = euclid' m n .fst

euclid≡euclid' : ∀ m n → euclid m n ≡ euclid' m n
euclid≡euclid' m n = isPropGCD (euclid m n) (euclid' m n)

gcd≡gcd' : ∀ m n → gcd m n ≡ gcd' m n
gcd≡gcd' m n = cong fst (euclid≡euclid' m n)


-- Bézout

bézout→isGCD : ∀ {m n : ℕ} (bz : ℤ.Bézout (pos m) (pos n)) → isGCD m n (abs (bz .ℤ.Bézout.gcd))
bézout→isGCD {m}{n} bz = (ℤ.∣→∣ℕ (bz .ℤ.Bézout.isCD .fst) , ℤ.∣→∣ℕ (bz .ℤ.Bézout.isCD .snd)) ,
  λ d' x → (ℤ.∣→∣ℕ ((ℤ.gcdIsGCD {pos m}{pos n} bz {pos d'}) (ℤ.∣ℕ→∣ (x .fst)) (ℤ.∣ℕ→∣ (x .snd))))

gcd≡absBézout : ∀ {m n : ℕ} (bz : ℤ.Bézout (pos m) (pos n)) →
  gcd m n ≡ abs (bz .ℤ.Bézout.gcd)
gcd≡absBézout {m}{n} bz = isGCD→gcd≡ (bézout→isGCD bz)

sign⊎ : ∀ m n → (Σ ℕ λ x → (ℤ.bézout (pos m) (pos n) .ℤ.Bézout.gcd) ≡ pos x)
              ⊎ (Σ ℕ λ x → (ℤ.bézout (pos m) (pos n) .ℤ.Bézout.gcd) ≡ negsuc x)
sign⊎ m n with (ℤ.bézout (pos m) (pos n) .ℤ.Bézout.gcd)
... | pos x  = inl (x , refl)
... | negsuc x  = inr (x , refl)

lemma-Bézout : ∀ m n → Σ ℤ (λ x → Σ ℤ (λ y →
  x ℤ.· (pos m) ℤ.+ y ℤ.· (pos n) ≡ (pos (gcd m n))))
lemma-Bézout m n with sign⊎ m n
lemma-Bézout m n | inl (x , prf)  =
  let bz = ℤ.bézout (pos m) (pos n)
      coef₁ = bz .ℤ.Bézout.coef₁
      coef₂ = bz .ℤ.Bézout.coef₂
      bz = ℤ.bézout (pos m) (pos n)
      res = bz .ℤ.Bézout.identity ∙ prf ∙
        (sym (cong (λ a → pos (abs a)) prf)) ∙ sym (cong pos (gcd≡absBézout bz))
  in  coef₁ , coef₂ , res
lemma-Bézout m n | inr (x , prf)  =
  let bz = ℤ.bézout (pos m) (pos n)
      coef₁ = bz .ℤ.Bézout.coef₁
      coef₂ = bz .ℤ.Bézout.coef₂
      bzgcd = bz .ℤ.Bézout.gcd
      bzid : coef₁ ℤ· (pos m) ℤ+ coef₂ ℤ· (pos n) ≡ bzgcd
      bzid = bz .ℤ.Bézout.identity
      step2 : -ℤ (coef₁ ℤ· (pos m) ℤ+ coef₂ ℤ· (pos n)) ≡ pos (gcd m n)
      step2 = cong -ℤ_ ((bz .ℤ.Bézout.identity) ∙ prf) ∙
        cong pos (injNegsuc (sym (cong (λ a → negsuc (abs a)) prf))) ∙
        (sym (cong pos (gcd≡absBézout bz)))
      step1 : -ℤ (coef₁ ℤ· (pos m) ℤ+ coef₂ ℤ· (pos n)) ≡
                (-ℤ coef₁) ℤ· pos m ℤ+ (-ℤ coef₂) ℤ· pos n
      step1 = -Dist+ (coef₁ ℤ· pos m) (coef₂ ℤ· pos n) ∙
        cong₂ (λ a b → a ℤ+ b) (-DistL· coef₁ (pos m)) (-DistL· coef₂ (pos n))
  in -ℤ coef₁ , -ℤ coef₂ , sym step1 ∙ step2

module Bézout where
  data Identity (d m n : ℕ) : Type where
    +- : (x y : ℕ) (eq : d + y · n ≡ x · m) → Identity d m n
    -+ : (x y : ℕ) (eq : d + x · m ≡ y · n) → Identity d m n

  private
    identityHlp : ∀ {m}{n} →
      (Σ ℤ λ x → Σ ℤ (λ y →
         x ℤ· pos (suc m) ℤ+ y ℤ· pos (suc n) ≡ pos (gcd (suc m) (suc n)))) →
      Identity (gcd (suc m) (suc n)) (suc m) (suc n)
    identityHlp {m} {n} (pos zero , pos zero , eq') =
      -+ zero zero ((+-comm (gcd (suc m) (suc n)) (zero · suc m)) ∙
         (sym (injPos ((pos·pos zero (suc n)) ∙
         pos0+ (pos zero ℤ· pos (suc n)) ∙ eq'))))
    identityHlp {m} {n} (pos zero , pos (suc y) , eq') =
      -+ zero (suc y) ((+-comm (gcd (suc m) (suc n)) (zero · suc m)) ∙
         (sym (injPos ((pos·pos (suc y) (suc n)) ∙
         pos0+ (pos (suc y) ℤ· pos (suc n)) ∙ eq'))))
    identityHlp {m} {n} (pos (suc x) , pos zero , eq') =
      +- (suc x) zero (+-comm (gcd (suc m) (suc n)) zero ∙
         sym (injPos (pos·pos (suc x) (suc m) ∙ eq')))
    identityHlp {m} {n} (pos (suc x) , pos (suc y) , eq') =
      ⊥.elim {ℓ-zero}{λ a → Identity (gcd (suc m) (suc n)) (suc m) (suc n)}
         (ℤ.isAsym< (subst (λ a → pos (suc m) ℤ.< a) eq' sucm<)
         (m≤n→posm≤posn (m∣n→m≤n snotz (gcd[m,n]∣m (suc m) (suc n)))))
      where
        step1 = cong (λ a → pos (suc m) ℤ.≤ pos (suc m) ℤ+ a) (pos·pos x (suc m))
        step2 = cong (λ a → pos 0 ℤ.< pos (suc n) ℤ+ a) (pos·pos y (suc n))
        step3 = subst (λ a → a) step2
          (ℤ.<-+-≤ {0}{pos (suc n)}{0}{pos (y · suc n)} zero-<sucPos ℤ.zero-≤pos)
        sucm< = ≤-+-< {pos (suc m)} {pos (suc m) ℤ+ pos x ℤ· pos (suc m)}{0}
          {(pos (suc n) ℤ+ pos y ℤ· pos (suc n))}
          (subst (λ a → a) step1 ((ℤ.≤SumLeftPos {pos (suc m)}{x · suc m}))) step3
    identityHlp {m} {n} (pos zero , negsuc y , eq') =
      ⊥.elim {ℓ-zero}{λ a → Identity (gcd (suc m) (suc n)) (suc m) (suc n)}
        (negsucNotpos (n + (y + n · y))
        (gcd (suc m) (suc n)) (sym (negsuc·possuc y n) ∙ pos0+ (negsuc y ℤ· pos (suc n)) ∙ eq'))
    identityHlp {m} {n} (pos (suc z) , negsuc y , eq') = +- (suc z) (suc y) step6
      where
        step1 = negsuc·possuc y n ∙ cong (λ a → negsuc (n + a)) (·-comm (suc n) y)
        step2 = pos+ (suc m) (z · suc m) ∙ cong (pos (suc m) ℤ+_) (pos·pos z (suc m))
        step3 = sym (cong₂ (λ a b → b ℤ.+ a) step1 (sym step2)) ∙ eq'
        step4 = +CancelRNegsuc (pos (suc (m + z · suc m)))
                 (n + y · suc n) (pos (gcd (suc m) (suc n))) step3
        step5 = sym (pos+ (gcd (suc m) (suc n)) (suc (n + y · suc n)))
        step6 = sym (injPos (step4 ∙ step5))
    identityHlp {n} {m} (negsuc y , pos z , eq') = -+ (suc y) z step6
      where
        step1 = negsuc·possuc y n ∙ cong (λ a → negsuc (n + a)) (·-comm (suc n) y)
        step2 = ℤ.+Comm (pos z ℤ· pos (suc m)) (negsuc y ℤ· pos (suc n)) ∙ eq'
        step3 = (sym (cong₂ (λ a b → a ℤ+ b) (sym (pos·pos z (suc m))) step1)) ∙ step2
        step4 = +CancelRNegsuc (pos (z · suc m))
                (n + y · suc n) (pos (gcd (suc n) (suc m))) step3
        step5 = sym (pos+ (gcd (suc n) (suc m)) (suc (n + y · suc n)))
        step6 = sym (injPos (step4 ∙ step5))
    identityHlp {m} {n} (negsuc z , negsuc y , eq') =
      ⊥.elim {ℓ-zero}  {λ x → Identity (gcd (suc m) (suc n)) (suc m) (suc n)}
        (negsucNotpos ((m + (suc m · z) + suc (n + suc n · y)))
        (gcd (suc m) (suc n)) ((sym (step1 ∙ step2)) ∙ eq' ))
      where
        step1 = cong₂ (λ a b → a ℤ+ b) (negsuc·possuc z m) (negsuc·possuc y n)
        step2 = negsuc+negsuc-def (m + (suc m · z)) {n + (suc n · y)}

    identity' : ∀ {m}{n} → Σ ℤ (λ x → Σ ℤ (λ y →
      x ℤ.· (pos m) ℤ.+ y ℤ.· (pos n) ≡ pos (gcd m n))) → Identity (gcd m n) m n
    identity' {ℕ.zero} {ℕ.zero} eq' = +- 0 0 refl
    identity' {ℕ.zero} {ℕ.suc n} eq' = -+ 0 1 refl
    identity' {ℕ.suc m} {ℕ.zero} eq' = +- 1 0 refl
    identity' m@{ℕ.suc m'} n@{ℕ.suc n'} (x , y , eq') = identityHlp {m'}{n'} (x , (y , eq'))

  identity : ∀ {m n d} → isGCD m n d → Identity d m n
  identity {m}{n}{d} mnd = subst (λ x → x)
    (cong (λ a → Identity a m n) (isGCD→gcd≡ mnd))
    (identity' {m}{n} (lemma-Bézout m n))

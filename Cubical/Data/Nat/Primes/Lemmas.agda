{-# OPTIONS --safe #-}

module Cubical.Data.Nat.Primes.Lemmas where

open import Cubical.Data.Nat.Primes.Imports
open import Cubical.Data.Empty as ⊥ hiding (elim)


private
    variable
        ℓ ℓ' ℓ'' : Level

-- some successive implication syntax

step⇒ : {A : Type ℓ} (B : Type ℓ') → (A → B) → A → B
step⇒ _ f = f

step⇒⟨⟩ : (A : Type ℓ) → A → A
step⇒⟨⟩ A a = a

syntax step⇒ B f x = x ⇒⟨ f ⟩ B
syntax step⇒⟨⟩ A a = a ⇒⟨⟩ A
infixl -9 step⇒ step⇒⟨⟩

-- auxiliary inequality, multiplication, divisibility lemmas

¬s<1 : ∀ {n} → ¬ suc n < 1
¬s<1 sn<1 with (<-split sn<1)
...     | inl sn<0 = ¬-<-zero sn<0
...     | inr sn=0 = snotz sn=0

¬z∣sn : ∀ n → ¬ 0 ∣ suc n
¬z∣sn n z∣sn = ⊥.rec (znots (∣-zeroˡ z∣sn))

¬<1∣sn : ∀ d n → d < 1 → ¬ d ∣ suc n
¬<1∣sn d n d<1 d∣sn with (<-split d<1)
...     | inr d=0 = ¬z∣sn n (subst (λ x → x ∣ suc n) d=0 (d∣sn))
...     | inl d<0 = ¬-<-zero d<0

1<→¬=0 : ∀ a → 1 < a → ¬ a ≡ 0
1<→¬=0 a (b , b+2=a) a=0 = snotz (+-comm 2 b ∙ b+2=a ∙ a=0)

<≠ : forall {m} {n} → m < n → ¬ m ≡ n
<≠ {m = m} m<n m=n = <-asym m<n (0 , sym m=n)

¬n<n : ∀ {n} → ¬ n < n
¬n<n n<n = <≠ n<n refl

z<suc : ∀ n → 0 < suc n
z<suc n = n , +-suc n 0 ∙ cong suc (+-zero n)

<1→0 : ∀ n → n < 1 → n ≡ 0
<1→0 n n<1 with (<-split n<1)
... | inr n=0 = n=0
... | inl n<0 = ⊥.rec (¬-<-zero n<0)

<<-asym : ∀ {a b} → a < b → ¬ b < a
<<-asym {a} {b} a<b b<a = ¬n<n (<-trans a<b b<a)

suc<-elim : ∀ {a} {b} → suc a < suc b → a < b
suc<-elim {a} {b} (n , n+sa=b) = n , injSuc (subst (λ x → x ≡ suc b) (+-suc n (suc a)) n+sa=b)

suc< : ∀ {a} {b} → a < b → suc a < suc b
suc< {a} {b} (n , n+sa=b) = n , subst (λ x → x ≡ suc b) (sym (+-suc n (suc a))) (cong suc n+sa=b)

add< : ∀ {a} {b} d → a < b → d + a < d + b
add< zero a<b = a<b
add< (suc d) a<b = suc< (add< d a<b)

mult< : ∀ k a b → a < b → a · suc k < b · suc k
mult< k a zero a<b = ⊥.rec (¬-<-zero a<b)
mult< k zero (suc b) a<b = z<suc (k + b · suc k)
mult< k (suc a) (suc b) a<b = suc< (add< k (mult< k a b (suc<-elim a<b)))

lem1 : ∀ c k d n → c < k → k · (suc d) < n → c · (suc d) < n
lem1 c k d n c<k ksd<n = <-trans (mult< d c k c<k) ksd<n

lem2 : ∀ c k d n → k < c → n < d + k · d → n < d + c · d
lem2 c k 0 n k<c n<k0 = ⊥.rec (¬-<-zero (subst (λ x → n < x) (sym (0≡m·0 k)) n<k0))
lem2 c k d@(suc d-1) n k<c n<d+kd = <-trans n<d+kd (add< d (mult< d-1 k c k<c))

sa<n : ∀ a n → suc a < n → a < n
sa<n a n (k , k+ssa=n) = k + 1 , subst (λ x → x ≡ n) (+-assoc k 1 (suc a)) k+ssa=n

+a<n : ∀ k a n → k + a < n → a < n
+a<n zero a n a<n = a<n
+a<n (suc k) a n sk+a<n = +a<n k a n (sa<n (k + a) n sk+a<n)

add-equations : ∀ {a} {b} {c} {d} → a ≡ b → c ≡ d → a + c ≡ b + d
add-equations {b = b} {c = c} a=b c=d = cong (_+ c) a=b ∙ cong (b +_) c=d

a·pos<n : ∀ a b n → a · suc b < n → a < n
a·pos<n zero b n z<sucn = z<sucn
a·pos<n (suc a) b zero asb<n = ⊥.rec (¬-<-zero asb<n)
a·pos<n (suc a) b (suc n) asb<n = suc< (a·pos<n a b n (+a<n b (a · suc b) n (suc<-elim asb<n)))

inj-·0< : ∀ {k} a b → 0 < k → k · a ≡ k · b → a ≡ b
inj-·0< {zero} _ _ 0<0 _ = ⊥.rec (¬n<n 0<0)
inj-·0< {suc k-1} a b 0<k = inj-sm· {m = k-1}

n≤n·pos : ∀ n k → 0 < k → n ≤ n · k
n≤n·pos n zero 0<0 = ⊥.rec (¬n<n 0<0)
n≤n·pos n (suc k) _ = subst (λ x → n ≤ x) (sym (·-comm n (suc k))) ≤SumLeft

1<·1<=3< : ∀ {a b} → 1 < a → 1 < b → 3 < a · b
1<·1<=3< {0} {0} 1<a 1<b = ⊥.rec (1<→¬=0 0 1<a refl)
1<·1<=3< {0} {suc b} 1<a 1<b = ⊥.rec (1<→¬=0 0 1<a refl)
1<·1<=3< {suc a} {0} 1<a 1<b = ⊥.rec (1<→¬=0 0 1<b refl)
1<·1<=3< {1} {suc b} 1<a 1<b = ⊥.rec (¬n<n 1<a)
1<·1<=3< {suc (suc a)} {1} 1<a 1<b = ⊥.rec (¬n<n 1<b)
1<·1<=3< {suc (suc a)} {suc (suc b)} 1<a 1<b =
    suc< (suc< (<≤-trans (suc< (z<suc (b + a · suc (suc b)))) (≤SumRight {k = b})))

PropFac< : ∀ a b n → 1 < b → 0 < n → a · b ≡ n → a < n
PropFac< zero _ _ _ 0<n _ = 0<n
PropFac< (suc a) zero n 1<b 0<n ab=n = ⊥.rec (¬-<-zero 1<b)
PropFac< (suc a) (suc zero) n 1<b 0<n ab=n = ⊥.rec (¬n<n 1<b)
PropFac< (suc a) (suc (suc b)) zero _ 0<n ab=n = ⊥.rec (¬n<n 0<n)
PropFac< (suc a) (suc (suc b)) (suc n) _ _ ab=n = lem a b n ab=n where
    lem : ∀ a b n → suc (suc (b + a · suc (suc b))) ≡ suc n → suc a < suc n
    lem a b n p =
        p :>                   suc (suc (b + a · suc (suc b))) ≡ suc n
        ⇒⟨ injSuc ⟩                  suc (b + a · suc (suc b)) ≡ n
        ⇒⟨ 0 ,_ ⟩                          b + a · suc (suc b) < n
        ⇒⟨ +a<n b (a · suc (suc b)) n ⟩        a · suc (suc b) < n
        ⇒⟨ a·pos<n a (suc b) n ⟩                             a < n
        ⇒⟨ suc< ⟩                                        suc a < suc n

∣+-cancel : ∀ n a b → n ∣ b → n ∣ (a + b) → n ∣ a
∣+-cancel n a b tn∣b tn∣a+b = n∣a where
    n∣b = ∣-untrunc tn∣b
    n∣a+b = ∣-untrunc tn∣a+b

    p = n∣b .fst
    pn=b = n∣b .snd

    q = n∣a+b .fst
    qn=a+b = n∣a+b .snd

    n∣a : n ∣ a
    n∣a = ∣ (q ∸ p) , (
            qn=a+b :>                                                    q · n ≡ a + b
            ⇒⟨ subst (λ x → q · n ≡ a + x) (sym pn=b) ⟩                  q · n ≡ a + p · n
            ⇒⟨ (λ x → cong (_∸ (p · n)) x ∙ +∸ a (p · n)) ⟩     q · n ∸ p · n ≡ a
            ⇒⟨ (∸-distribʳ q p n) ∙_ ⟩                            (q ∸ p) · n ≡ a )
         ∣₁


ab=1→1 : ∀ a b → a · b ≡ 1 → b ≡ 1
ab=1→1 0 0 ab=1 = ab=1
ab=1→1 0 (suc b) ab=1 = ⊥.rec (znots ab=1)
ab=1→1 (suc a) 0 ab=1 = ·-comm 0 a ∙ ab=1
ab=1→1 (suc a) 1 _ = refl
ab=1→1 (suc a) (suc (suc b)) ab=1 = ⊥.rec (snotz (injSuc ab=1))

div1→1 : ∀ n → n ∣ 1 → n ≡ 1
div1→1 n ∣n∣1∣ = ab=1→1 k n kn=1 where
    n∣1 : Σ[ k ∈ ℕ ] k · n ≡ 1
    n∣1 = ∣-untrunc ∣n∣1∣
    k = n∣1 .fst
    kn=1 = n∣1 .snd

-- decidability lemmas

Dec-1<k : ∀ k → Dec (1 < k)
Dec-1<k k with (1 ≟ k)
...     | lt 1<k = yes 1<k
...     | eq 1=k = no (λ x → <≠ x 1=k)
...     | gt k<1 = no (<<-asym k<1)

Dec-k∣n :  ∀ {n} k → Dec (k ∣ n)
Dec-k∣n {0} k = yes (∣-zeroʳ k)
Dec-k∣n {n@(suc n-1)} k with (any? {n = n} (λ (x , _) → discreteℕ (x · k) n))
...     | yes ((x , x<n) , xk=n) = yes (∣ (x , xk=n) ∣₁)
...     | no bad with k
...     | 0 = no (λ |ddiv| → ¬-<-zero (subst
                                      (λ x → 0 < x)
                                      (sym (subst
                                           (λ x → 0 ≡ n)
                                           (sym (0≡m·0 (fst (∣-untrunc |ddiv|))))
                                           (snd (∣-untrunc |ddiv|))))
                                       (z<suc n-1)))
...     | 1 = yes (∣ n , ·-identityʳ n ∣₁)
...     | suc (suc k) = no (λ |ddiv| → bad
            ((fst (∣-untrunc |ddiv|) ,
            PropFac< (fst (∣-untrunc |ddiv|)) (suc (suc k)) n
                     (suc< (z<suc k)) (z<suc n-1) (snd (∣-untrunc |ddiv|))) ,
            snd (∣-untrunc |ddiv|)))

HasFactor : (n k : ℕ) → Type
HasFactor n k = (1 < k) × (k ∣ n)

DecHF : ∀ {n} k → Dec (HasFactor n k)
DecHF k with (Dec-1<k k) | (Dec-k∣n k)
... | (yes 1<k) | (yes k∣n) = yes (1<k , k∣n)
... | (yes 1<k) | (no ¬k∣n) = no (λ (_ , k∣n) → ¬k∣n k∣n)
... | (no ¬1<k) | _        = no (λ (1<k , _) → ¬1<k 1<k)

-- find least natural with a given property, assuming there is one
-- essentially the well-ordering principle: any inhabited subset has a least element

findLeast-worker :
        {n : ℕ} →
        ({x : ℕ} → (x < n) → {P : ℕ → Type ℓ} → P x → (∀ a → Dec (P a)) →
        Σ[ least ∈ ℕ ] (P least) × (∀ z → P z → least ≤ z)) →
        {P : ℕ → Type ℓ} → P n → (∀ a → Dec (P a)) →
        Σ[ least ∈ ℕ ] (P least) × (∀ z → P z → least ≤ z)
findLeast-worker {n = zero} rec P0 Pdec = zero , (P0 , (λ _ _ → zero-≤))
findLeast-worker {n = n@(suc n-1)} rec {P = P} Pn Pdec with any? {n = n} Qdec where
    Qdec : ∀ ((x , x<n) : Fin n) → Dec (P x)
    Qdec (x , x<n) = Pdec x
... | yes ((x , x<n) , Px) = rec x<n Px Pdec
... | no ¬x,x<n,Px = n , Pn , least where
        least : ∀ x → P x → n ≤ x
        least x Px with (Dichotomyℕ n x)
        ... | inl n≤x = n≤x
        ... | inr x<n = ⊥.rec (¬x,x<n,Px ((x , x<n) , Px))

findLeast-explicit : (n : ℕ) → (P : ℕ → Type ℓ) → P n → (∀ a → Dec (P a)) →
                     Σ[ least ∈ ℕ ] (P least) × (∀ z → P z → least ≤ z)
findLeast-explicit = WFI.induction <-wellfounded
                     (λ n rec P → findLeast-worker {n = n} (λ {x} x<n {P} → rec x x<n P) {P})

findLeast : {n : ℕ} → {P : ℕ → Type ℓ} → P n → (∀ a → Dec (P a)) →
            Σ[ least ∈ ℕ ] (P least) × (∀ z → P z → least ≤ z)
findLeast {n = n} {P = P} = findLeast-explicit n P

-- product and factorial lemmas for newPrime

product : List ℕ → ℕ
product [] = 1
product (x ∷ xs) = x · product xs

0<factorial : ∀ n → 0 < n !
0<factorial 0 = z<suc 0
0<factorial (suc n) = <≤-trans (0<factorial n) ≤SumLeft

n≤! : ∀ n → n ≤ (n !)
n≤! 0 = 1 , refl
n≤! (suc n) = n≤n·pos (suc n) (n !) (0<factorial n)

0<n∣n! : ∀ n → ¬ n ≡ 0 → n ∣ (n !)
0<n∣n! zero ¬n=0 = ⊥.rec (¬n=0 refl)
0<n∣n! (suc n) ¬n=0 = ∣ (n ! , ·-comm (n !) (suc n)) ∣₁

≤n∣n! : ∀ a n → a ≤ n → ¬ a ≡ 0 → a ∣ (n !)
≤n∣n! a zero a≤n ¬a=0 = ⊥.rec (¬a=0 (≤0→≡0 a≤n))
≤n∣n! a (suc n) a≤sn na=0 with ≤-split a≤sn
... | inr a=sn = subst (λ x → x ∣ ((suc n) !)) (sym a=sn) (0<n∣n! (suc n) snotz)
... | inl (k , k+sa=sn) = ∣-trans a∣n! ∣ ((suc n) , refl) ∣₁ where
    a∣n! : a ∣ (n !)
    a∣n! = ≤n∣n! a n (k , injSuc (sym (+-suc k a) ∙ k+sa=sn)) na=0

-- All

data All {A : Type ℓ} (P : A → Type ℓ') : List A → Type (ℓ-max ℓ ℓ') where
  []  :                             All P []
  _∷_ : ∀ {x xs} → P x → All P xs → All P (x ∷ xs)

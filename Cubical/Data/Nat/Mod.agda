{-# OPTIONS --cubical #-}
module Cubical.Data.Nat.Mod where

open import Agda.Builtin.Nat using () renaming (
  div-helper to hdiv ;
  mod-helper to hmod)
open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Empty
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎

-- Defining x mod 0 to be 0. This way all the theorems below are true
-- for n : ℕ instead of n : ℕ₊₁.

------ Preliminary definitions ------
modInd : (n : ℕ) → ℕ → ℕ
modInd n = +induction n (λ _ → ℕ) (λ x _ → x) λ _ x → x

modIndBase : (n m : ℕ) → m < suc n → modInd n m ≡ m
modIndBase n = +inductionBase n (λ _ → ℕ) (λ x _ → x) (λ _ x → x)

modIndStep : (n m : ℕ) → modInd n (suc n + m) ≡ modInd n m
modIndStep n = +inductionStep n (λ _ → ℕ) (λ x _ → x) (λ _ x → x)
-------------------------------------

_mod_ : (x n : ℕ) → ℕ
x mod zero = 0
x mod (suc n) = modInd n x

mod< : (n x : ℕ) → x mod (suc n) < (suc n)
mod< n =
  +induction n
    (λ x → x mod (suc n) < suc n)
    (λ x base → fst base
               , (cong (λ x → fst base + suc x)
                       (modIndBase n x base)
                ∙ snd base))
     λ x ind → fst ind
              , cong (λ x → fst ind + suc x)
                     (modIndStep n x) ∙ snd ind


<→mod : (n x : ℕ) → x < (suc n) → x mod (suc n) ≡ x
<→mod = modIndBase

mod-rUnit : (n x : ℕ) → x mod n ≡ ((x + n) mod n)
mod-rUnit zero x = refl
mod-rUnit (suc n) x =
    sym (modIndStep n x)
  ∙ cong (modInd n) (+-comm (suc n) x)

mod-lUnit : (n x : ℕ) → x mod n ≡ ((n + x) mod n)
mod-lUnit zero _ = refl
mod-lUnit (suc n) x = sym (modIndStep n x)

mod+mod≡mod : (n x y : ℕ)
  → (x + y) mod n ≡ (((x mod n) + (y mod n)) mod n)
mod+mod≡mod zero _ _ = refl
mod+mod≡mod (suc n) =
  +induction n
    (λ z → (x : ℕ)
         → ((z + x) mod (suc n))
         ≡ (((z mod (suc n)) + (x mod (suc n))) mod (suc n)))
    (λ x p →
      +induction n _
        (λ y q → cong (modInd n)
                       (sym (cong₂  _+_ (modIndBase n x p)
                       (modIndBase n y q))))
        λ y ind → cong (modInd n)
                        (cong (x +_) (+-comm (suc n) y)
                                   ∙ (+-assoc x y (suc n)))
                     ∙∙ sym (mod-rUnit (suc n) (x + y))
                     ∙∙ ind
                      ∙ cong (λ z → modInd n
                                    ((modInd n x + z)))
                             (mod-rUnit (suc n) y
                             ∙ cong (modInd n) (+-comm y (suc n))))
    λ x p y →
      cong (modInd n) (cong suc (sym (+-assoc n x y)))
        ∙∙ sym (mod-lUnit (suc n) (x + y))
        ∙∙ p y
         ∙ sym (cong (modInd n)
                (cong (_+ modInd n y)
                 (cong (modInd n)
                  (+-comm (suc n) x) ∙ sym (mod-rUnit (suc n) x))))

mod-idempotent : {n : ℕ} (x : ℕ) → (x mod n) mod n ≡ x mod n
mod-idempotent {n = zero} _ = refl
mod-idempotent {n = suc n} =
  +induction n (λ x → (x mod suc n) mod (suc n) ≡ x mod (suc n))
             (λ x p → cong (_mod (suc n))
                            (modIndBase n x p))
              λ x p → cong (_mod (suc n))
                            (modIndStep n x)
                          ∙∙ p
                          ∙∙ mod-rUnit (suc n) x
                           ∙ (cong (_mod (suc n)) (+-comm x (suc n)))

zero-charac : (n : ℕ) → n mod n ≡ 0
zero-charac zero = refl
zero-charac (suc n) = cong (_mod suc n) (+-comm 0 (suc n))
                  ∙∙ modIndStep n 0
                  ∙∙ modIndBase n 0 (n , (+-comm n 1))

zero-charac-gen : (n x : ℕ) → ((x · n) mod n) ≡ 0
zero-charac-gen zero x = refl
zero-charac-gen (suc n) zero = refl
zero-charac-gen (suc n) (suc x) =
  modIndStep n (x · (suc n)) ∙ zero-charac-gen (suc n) x

mod·mod≡mod : (n x y : ℕ)
  → (x · y) mod n ≡ (((x mod n) · (y mod n)) mod n)
mod·mod≡mod zero _ _ = refl
mod·mod≡mod (suc n) =
  +induction n _
    (λ x p → +induction n _
      (λ y q
        → cong (modInd n)
            (cong₂ _·_ (sym (modIndBase n x p)) (sym (modIndBase n y q))))
      λ y p →
           cong (modInd n) (sym (·-distribˡ  x (suc n) y))
        ∙∙ mod+mod≡mod (suc n) (x · suc n) (x · y)
        ∙∙ cong (λ z → modInd n (z + modInd n (x · y)))
                (zero-charac-gen (suc n) x)
        ∙∙ mod-idempotent (x · y)
        ∙∙ p
         ∙ cong (_mod (suc n)) (cong (x mod (suc n) ·_)
                (sym (mod-idempotent y)
                ∙∙ (λ i → modInd n (mod-rUnit (suc n) 0 i + modInd n y))
                ∙∙ sym (mod+mod≡mod (suc n) (suc n) y))))
    λ x p y →
         (sym (cong (_mod (suc n)) (·-distribʳ (suc n) x y))
       ∙∙ mod+mod≡mod (suc n) (suc n · y) (x · y)
       ∙∙ (λ i → modInd n ((cong (_mod (suc n))
             (·-comm (suc n) y) ∙ zero-charac-gen (suc n) y) i
             + modInd n (x · y)))
        ∙ mod-idempotent (x · y))
      ∙∙ p y
      ∙∙ cong (_mod (suc n)) (cong (_· y mod (suc n))
              ((sym (mod-idempotent x)
              ∙ cong (λ z → (z + x mod (suc n)) mod (suc n))
                     (mod-rUnit (suc n) 0))
              ∙ sym (mod+mod≡mod (suc n) (suc n) x)))

mod-rCancel : (n x y : ℕ) → (x + y) mod n ≡ (x + y mod n) mod n
mod-rCancel zero x y = refl
mod-rCancel (suc n) x =
  +induction n _
    (λ y p → cong (λ z → (x + z) mod (suc n))
                   (sym (modIndBase n y p)))
     λ y p → cong (_mod suc n) (+-assoc x (suc n) y
                             ∙∙ (cong (_+ y) (+-comm x (suc n)))
                             ∙∙ sym (+-assoc (suc n) x y))
          ∙∙ sym (mod-lUnit (suc n) (x + y))
          ∙∙ (p ∙ cong (λ z → (x + z) mod suc n) (mod-lUnit (suc n) y))

mod-lCancel : (n x y : ℕ) → (x + y) mod n ≡ (x mod n + y) mod n
mod-lCancel n x y =
     cong (_mod n) (+-comm x y)
  ∙∙ mod-rCancel n y x
  ∙∙ cong (_mod n) (+-comm y (x mod n))

-- remainder and quotient after division by n
-- Again, allowing for 0-division to get nicer syntax
remainder_/_ : (x n : ℕ) → ℕ
remainder x / zero = x
remainder x / suc n = x mod (suc n)

quotient_/_ : (x n : ℕ) → ℕ
quotient x / zero = 0
quotient x / suc n =
  +induction n (λ _ → ℕ) (λ _ _ → 0) (λ _ → suc) x

≡remainder+quotient : (n x : ℕ)
  → (remainder x / n) + n · (quotient x / n) ≡ x
≡remainder+quotient zero x = +-comm x 0
≡remainder+quotient (suc n) =
  +induction n
    (λ x → (remainder x / (suc n)) + (suc n)
          · (quotient x / (suc n)) ≡ x)
    (λ x base → cong₂ _+_ (modIndBase n x base)
                           (cong ((suc n) ·_)
                           (+inductionBase n _ _ _ x base))
              ∙∙ cong (x +_) (·-comm n 0)
              ∙∙ +-comm x 0)
     λ x ind → cong₂ _+_ (modIndStep n x)
                        (cong ((suc n) ·_) (+inductionStep n _ _ _ x))
          ∙∙ cong (modInd n x +_)
                  (·-suc (suc n) (+induction n _ _ _ x))
          ∙∙ cong (modInd n x +_)
                  (+-comm (suc n) ((suc n) · (+induction n _ _ _ x)))
          ∙∙ +-assoc (modInd n x) ((suc n) · +induction n _ _ _ x) (suc n)
          ∙∙ cong (_+ suc n) ind
           ∙ +-comm x (suc n)

-- Alternative definitions of quotient_/_ and remainder_/_

-- helper lemmas to prove some of their properties
private
  div-mod-lemma : ∀ accᵐ accᵈ d n →
    accᵐ + accᵈ · suc (accᵐ + n) + d
    ≡
    hmod accᵐ (accᵐ + n) d n + hdiv accᵈ (accᵐ + n) d n · suc (accᵐ + n)
  div-mod-lemma accᵐ accᵈ zero    n       = +-zero _
  div-mod-lemma accᵐ accᵈ (suc d) zero    =
    (accᵐ + accᵈ · suc (accᵐ + zero)) + suc d          ≡⟨ step0 ⟩
    suc (accᵐ + accᵈ · suc (accᵐ + zero)) + d          ≡⟨⟩
    ((suc accᵐ) + accᵈ · suc (accᵐ + zero)) + d        ≡⟨ step1 ⟩
    ((suc accᵐ) + accᵈ · (suc accᵐ)) + d               ≡⟨⟩
    0 + (suc accᵈ) · suc (0 + accᵐ) + d                ≡⟨ step2 ⟩
    hmod 0 (0 + accᵐ) d accᵐ +
    hdiv (suc accᵈ) (0 + accᵐ) d accᵐ · suc (0 + accᵐ) ≡⟨⟩
    hmod 0 accᵐ d accᵐ +
    hdiv (suc accᵈ) accᵐ d accᵐ · suc accᵐ             ≡⟨⟩
    hmod accᵐ accᵐ (suc d) 0 +
    hdiv accᵈ accᵐ (suc d) 0 · suc accᵐ                ≡⟨ step3 ⟩
    hmod accᵐ (accᵐ + 0) (suc d) 0 +
    hdiv accᵈ (accᵐ + 0) (suc d) 0 · suc (accᵐ + 0)    ∎
      where
        step0 = +-suc _ d
        step1 = λ i → ((suc accᵐ) + accᵈ · suc (+-zero accᵐ i)) + d
        step2 = div-mod-lemma 0 (suc accᵈ) d accᵐ
        step3 = cong (λ p → hmod accᵐ p (suc d) 0 + hdiv accᵈ p (suc d) 0 · suc p)
                     (sym (+-zero accᵐ))
  div-mod-lemma accᵐ accᵈ (suc d) (suc n) =
    (accᵐ + accᵈ · suc (accᵐ + suc n)) + suc d          ≡⟨ step0 ⟩
    (suc (accᵐ + accᵈ · suc (accᵐ + suc n))) + d        ≡⟨⟩
    ((suc accᵐ) + accᵈ · suc (accᵐ + suc n)) + d        ≡⟨ step1 ⟩
    ((suc accᵐ) + accᵈ · suc ((suc accᵐ) + n)) + d      ≡⟨ step2 ⟩
    hmod (suc accᵐ) (suc accᵐ + n) d n +
    hdiv accᵈ (suc accᵐ + n) d n · suc (suc accᵐ + n)   ≡⟨ step3 ⟩
    hmod (suc accᵐ) (accᵐ + suc n) d n +
    hdiv accᵈ (accᵐ + suc n) d n · suc (accᵐ + suc n)   ≡⟨⟩
    hmod accᵐ (accᵐ + suc n) (suc d) (suc n) +
    hdiv accᵈ (accᵐ + suc n) (suc d) (suc n) · suc (accᵐ + suc n) ∎
      where
        step0 = +-suc _ d
        step1 = λ i → ((suc accᵐ) + accᵈ · suc (+-suc accᵐ n i)) + d
        step2 = div-mod-lemma (suc accᵐ) accᵈ d n
        step3 = cong (λ p → hmod (suc accᵐ) p d n + hdiv accᵈ p d n · suc p)
                     (sym (+-suc accᵐ n))

  mod-lemma-≤ : ∀ acc d n → hmod acc (acc + n) d n ≤ acc + n
  mod-lemma-≤ acc zero    n       = ≤SumLeft
  mod-lemma-≤ acc (suc d) zero    = mod-lemma-≤ 0 d (acc + 0)
  mod-lemma-≤ acc (suc d) (suc n) =
    hmod acc (acc + suc n) (suc d) (suc n) ≡≤⟨ step0 ⟩
    hmod acc (suc acc + n) (suc d) (suc n) ≡≤⟨ refl ⟩
    hmod (suc acc) (suc acc + n) d n       ≤≡⟨ step1 ⟩
    suc acc + n                            ≡⟨ step2 ⟩
    acc + (suc n)                          ∎
    where
      open <-Reasoning
      step0 = λ i → hmod acc (+-suc acc n i) (suc d) (suc n)
      step1 = mod-lemma-≤ (suc acc) d n
      step2 = sym (+-suc acc n)

remainder'_/_ : (x n : ℕ) → ℕ
remainder' x / zero = x
remainder' x / suc n = hmod 0 n x n

quotient'_/_ : (x n : ℕ) → ℕ
quotient' x / zero = 0
quotient' x / suc n = hdiv 0 n x n

≡remainder'+quotient' : (n x : ℕ)
  → (remainder' x / n) + n · (quotient' x / n) ≡ x
≡remainder'+quotient' zero    x = +-zero x
≡remainder'+quotient' (suc n) x =
  remainder' x / suc n + suc n · (quotient' x / suc n)  ≡⟨ step0 ⟩
  remainder' x / suc n + quotient' x / suc n · suc n    ≡⟨⟩
  hmod 0 n x n + hdiv 0 n x n · suc n                   ≡⟨⟩
  hmod 0 (0 + n) x n + hdiv 0 (0 + n) x n · suc (0 + n) ≡⟨ step1 ⟩
  x                                                     ∎
    where
      step0 = cong (remainder' x / suc n +_) (·-comm (suc n) (quotient' x / suc n))
      step1 = sym ( div-mod-lemma 0 0 x n )

mod'< : ∀ n x → remainder' x / suc n < suc n
mod'< n x = suc-≤-suc (mod-lemma-≤ 0 x n)

private
  test₀ : 100 mod 81 ≡ 19
  test₀ = refl

  test₁ : ((11 + (10 mod 3)) mod 3) ≡ 0
  test₁ = refl



·mod : ∀ k n m → (k · n) mod (k · m)
             ≡ k · (n mod m)
·mod zero n m = refl
·mod (suc k) n zero = cong ((n + k · n) mod_) (sym (0≡m·0 (suc k)))
                  ∙ 0≡m·0 (suc k)
·mod (suc k) n (suc m) = ·mod' n n ≤-refl (splitℕ-≤ (suc m) n)

 where
 ·mod' : ∀ N n → n ≤ N → ((suc m) ≤ n) ⊎ (n < suc m) →
    ((suc k · n) mod (suc k · suc m)) ≡ suc k · (n mod suc m)
 ·mod' _ zero x _ = cong (modInd (m + k · suc m)) (sym (0≡m·0 (suc k)))
                  ∙ 0≡m·0 (suc k)
 ·mod' zero (suc n) x _ = ⊥.rec (¬-<-zero x)
 ·mod' (suc N) n@(suc n') x (inl (m' , p)) =
  let z = ·mod' N m' (≤-trans (m
               , +-comm m m' ∙ injSuc (sym (+-suc m' m) ∙ p))
              (pred-≤-pred x)) (splitℕ-≤ _ _) ∙ cong ((suc k) ·_)
            (sym (modIndStep m m') ∙
             cong (_mod (suc m)) (+-comm (suc m) m' ∙ p))
  in (cong (λ y → ((suc k · y) mod (suc k · suc m))) (sym p)
       ∙ cong {x = (m' + suc m + k · (m' + suc m))}
               {suc (m + k · suc m + (m' + k · m'))}
            (modInd (m + k · suc m))
              (cong (_+ k · (m' + suc m)) (+-suc m' m ∙ cong suc (+-comm m' m))
                 ∙ cong suc
                  (sym (+-assoc m m' _)
                    ∙∙ cong (m +_)
                       (((cong (m' +_) (sym (·-distribˡ k _ _)
                         ∙ +-comm (k · m') _) ∙ +-assoc m' (k · suc m) (k · m'))
                        ∙ cong (_+ k · m') (+-comm m' _))
                        ∙ sym (+-assoc (k · suc m) m' (k · m')) )
                    ∙∙ +-assoc m _ _))
         ∙ modIndStep (m + k · suc m) (m' + k · m')) ∙ z
 ·mod' (suc N) n x (inr x₁) =
   modIndBase _ _ (
     subst2 _<_ (·-comm n (suc k)) (·-comm _ (suc k))
      (<-·sk {n} {suc m} {k = k} x₁) )
    ∙ cong ((suc k) ·_) (sym (modIndBase _ _ x₁))

2≤x→1<quotient[x/2] : ∀ n → 0 < quotient (2 + n) / 2
2≤x→1<quotient[x/2] n =
 let z : 0 < ((quotient (2 + n) / 2) · 2)
     z = subst (0 <_) (·-comm 2 (quotient (2 + n) / 2))
          (≤<-trans {m = n }
             {n = 2 · (quotient (2 + n) / 2)} zero-≤
            (<-k+-cancel (subst (_< 2 +
             (2 · (quotient (2 + n) / 2)))
           (≡remainder+quotient 2 (2 + n))
             (<-+k {k = 2 · (quotient (2 + n) / 2)}
              (mod< 1 (2 + n))))))
 in <-·sk-cancel {0} {quotient (2 + n) / 2 } {k = 1} z



2≤x→quotient[x/2]<x : ∀ n → quotient (2 + n) / 2 < (2 + n)
2≤x→quotient[x/2]<x n =
  subst ((quotient 2 + n / 2) <_)
    (≡remainder+quotient 2 (2 + n))
    (<≤-trans
      ( subst ((quotient 2 + n / 2) <_)
          ((cong ((quotient 2 + n / 2) +_)
            (sym (+-zero (quotient 2 + n / 2)))))
            (<-+k {k = (quotient 2 + n / 2)}
             (2≤x→1<quotient[x/2] n)) )
      (≤SumRight {_} {(remainder 2 + n / 2)}))

open Minimal

log2ℕ : ∀ n → Σ _ (Least (λ k → n < 2 ^ k))
log2ℕ n = w n n ≤-refl
 where

  w : ∀ N n → n ≤ N
          → Σ _ (Least (λ k → n < 2 ^ k))
  w N zero x = 0 , (≤-refl , λ k' q → ⊥.rec (¬-<-zero q))
  w N (suc zero) x = 1 , (≤-refl ,
     λ { zero q → <-asym (suc-≤-suc ≤-refl)
      ; (suc k') q → ⊥.rec (¬-<-zero (pred-≤-pred q))})
  w zero (suc (suc n)) x = ⊥.rec (¬-<-zero x)
  w (suc N) (suc (suc n)) x =
   let (k , (X , Lst)) = w N
          (quotient 2 + n / 2)
          (≤-trans (pred-≤-pred (2≤x→quotient[x/2]<x n))
             (pred-≤-pred x))
       z = ≡remainder+quotient 2 (2 + n)
       zz = <-+-≤ X X
       zzz : suc (suc n) < (2 ^ suc k)
       zzz = subst2 (_<_)
           (+-comm (quotient 2 + n / 2) ((remainder 2 + n / 2) + (quotient 2 + n / 2))
              ∙ sym (+-assoc ((remainder 2 + n / 2)) (quotient 2 + n / 2) (quotient 2 + n / 2))
               ∙ cong ((remainder 2 + n / 2) +_)
             ((cong ((quotient 2 + n / 2) +_)
              (sym (+-zero (quotient 2 + n / 2)))))
             ∙ z)
           (cong ((2 ^ k) +_) (sym (+-zero (2 ^ k))))
           (≤<-trans
             (≤-k+ (≤-+k (pred-≤-pred (mod< 1 (2 + n))))) zz)
   in (suc k)
       , zzz
        , λ { zero 0'<sk 2+n<2^0' →
                ⊥.rec (¬-<-zero (pred-≤-pred 2+n<2^0'))
            ; (suc k') k'<sk 2+n<2^k' →
               Lst k' (pred-≤-pred k'<sk)
                (<-·sk-cancel {k = 1}
                    (subst2 _<_ (·-comm 2 (quotient 2 + n / 2)) (·-comm 2 (2 ^ k'))
                      (≤<-trans  ((remainder 2 + n / 2) , z)
                         2+n<2^k' )))}

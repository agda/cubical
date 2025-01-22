{-# OPTIONS --safe --lossy-unification #-}

module Cubical.HITs.CauchyReals.Sequence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Nat as ℕ hiding (_·_;_+_)
import Cubical.Data.Nat.Mod as ℕ
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Int as ℤ using (pos)
import Cubical.Data.Int.Order as ℤ
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Data.NatPlusOne

open import Cubical.Data.Rationals as ℚ using (ℚ ; [_/_])
open import Cubical.Data.Rationals.Order as ℚ using
  ( _ℚ₊+_ ; 0<_ ; ℚ₊ ; _ℚ₊·_ ; ℚ₊≡)
open import Cubical.Data.Rationals.Order.Properties as ℚ
 using (invℚ₊;/2₊;/3₊;/4₊;x/2<x;invℚ;_ℚ^ⁿ_;_ℚ₊^ⁿ_)


open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Lems
open import Cubical.HITs.CauchyReals.Closeness
open import Cubical.HITs.CauchyReals.Lipschitz
open import Cubical.HITs.CauchyReals.Order
open import Cubical.HITs.CauchyReals.Continuous
open import Cubical.HITs.CauchyReals.Multiplication
open import Cubical.HITs.CauchyReals.Inverse





Seq : Type
Seq = ℕ → ℝ


≤ᵣ-·ᵣo : ∀ m n o → 0 ≤ᵣ o  →  m ≤ᵣ n → (m ·ᵣ o ) ≤ᵣ (n ·ᵣ o)
≤ᵣ-·ᵣo m n o 0≤o m≤n = subst (λ o →
   (m ·ᵣ o ) ≤ᵣ (n ·ᵣ o)) 0≤o (w ∙
      cong (_·ᵣ maxᵣ (rat [ pos 0 / 1+ 0 ]) o) m≤n)
 where
 w : maxᵣ (m ·ᵣ maxᵣ 0 o ) (n ·ᵣ maxᵣ 0 o) ≡  (maxᵣ m n ·ᵣ maxᵣ 0 o)
 w = ≡Continuous _ _
     (cont₂maxᵣ _ _
       ((IsContinuous∘ _ _
         (IsContinuous·ᵣL m) (IsContinuousMaxL 0)  ))
       ((IsContinuous∘ _ _
         (IsContinuous·ᵣL n) (IsContinuousMaxL 0)  )))
     (IsContinuous∘ _ _
         (IsContinuous·ᵣL _) (IsContinuousMaxL 0)  )
      (λ o' →
        ≡Continuous _ _
          (IsContinuous∘ _ _ (IsContinuousMaxR ((n ·ᵣ maxᵣ 0 (rat o'))))
                (IsContinuous·ᵣR (maxᵣ 0 (rat o'))) )
          (IsContinuous∘ _ _  (IsContinuous·ᵣR (maxᵣ 0 (rat o')))
                                (IsContinuousMaxR n))
          (λ m' →
            ≡Continuous
              (λ n → maxᵣ (rat m' ·ᵣ maxᵣ 0 (rat o') ) (n ·ᵣ maxᵣ 0 (rat o')))
              (λ n →  maxᵣ (rat m') n ·ᵣ maxᵣ 0 (rat o'))
              ((IsContinuous∘ _ _
                (IsContinuousMaxL (((rat m') ·ᵣ maxᵣ 0 (rat o'))))
                (IsContinuous·ᵣR (maxᵣ 0 (rat o'))) ))
              (IsContinuous∘ _ _ ((IsContinuous·ᵣR (maxᵣ 0 (rat o'))))
                  (IsContinuousMaxL (rat m')))
              (λ n' →
                 (cong₂ maxᵣ (sym (rat·ᵣrat _ _)) (sym (rat·ᵣrat _ _)))
                  ∙∙ cong rat (sym (ℚ.·MaxDistrℚ' m' n' (ℚ.max 0 o')
                      (ℚ.≤max 0 o'))) ∙∙
                  rat·ᵣrat _ _
                 ) n) m) o

≤ᵣ-o·ᵣ : ∀ m n o → 0 ≤ᵣ o →  m ≤ᵣ n → (o ·ᵣ m   ) ≤ᵣ (o ·ᵣ n)
≤ᵣ-o·ᵣ m n o 0≤o p = subst2 _≤ᵣ_
  (·ᵣComm _ _)
  (·ᵣComm _ _)
  (≤ᵣ-·ᵣo m n o 0≤o p)

≤ᵣ₊Monotone·ᵣ : ∀ m n o s → 0 ≤ᵣ n → 0 ≤ᵣ o
       → m ≤ᵣ n → o ≤ᵣ s
       → (m ·ᵣ o) ≤ᵣ (n ·ᵣ s)
≤ᵣ₊Monotone·ᵣ m n o s 0≤n 0≤o m≤n o≤s =
  isTrans≤ᵣ _ _ _ (≤ᵣ-·ᵣo m n o 0≤o m≤n)
    (≤ᵣ-o·ᵣ o s n 0≤n o≤s)




ℝ₊· : (m : ℝ₊) (n : ℝ₊) → 0 <ᵣ (fst m) ·ᵣ (fst n)
ℝ₊· (m , 0<m) (n , 0<n) = PT.map2
  (λ ((q , q') , 0≤q , q<q' , q'≤m) →
   λ ((r , r') , 0≤r , r<r' , r'≤n) →
    let 0<r' = ℚ.isTrans≤< _ _ _ (≤ᵣ→≤ℚ 0 r 0≤r) r<r'
        qr₊ = (q' , ℚ.<→0< _ (ℚ.isTrans≤< _ _ _ (≤ᵣ→≤ℚ 0 q 0≤q) q<q'))
               ℚ₊· (r' , ℚ.<→0< _ 0<r')
    in (fst (/2₊ qr₊) , fst qr₊) ,
         ≤ℚ→≤ᵣ _ _ (ℚ.0≤ℚ₊ (/2₊ qr₊)) ,
           x/2<x qr₊ ,
           subst (_≤ᵣ (m ·ᵣ n))
             (sym (rat·ᵣrat q' r'))
              (≤ᵣ₊Monotone·ᵣ (rat q')
                (m) (rat r') n (<ᵣWeaken≤ᵣ _ _ 0<m)
                               (<ᵣWeaken≤ᵣ _ _ (<ℚ→<ᵣ _ _ 0<r'))
                             q'≤m r'≤n) ) 0<m 0<n

_₊+ᵣ_ : ℝ₊ → ℝ₊ → ℝ₊
(m , 0<m) ₊+ᵣ (n , 0<n) = m +ᵣ n , <ᵣMonotone+ᵣ 0 m 0 n 0<m 0<n

_₊·ᵣ_ : ℝ₊ → ℝ₊  → ℝ₊
(m , 0<m) ₊·ᵣ (n , 0<n) = _ , ℝ₊· (m , 0<m) (n , 0<n)

_₊／ᵣ₊_ : ℝ₊ → ℝ₊  → ℝ₊
(q , 0<q) ₊／ᵣ₊ (r , 0<r) = (q ／ᵣ[ r , inl (0<r) ] ,
  ℝ₊· (q , 0<q) (_ , invℝ-pos r 0<r) )




0<1/x : ∀ x 0＃x → 0 <ᵣ x → 0 <ᵣ invℝ x 0＃x
0<1/x x 0＃x 0<x = subst (0 <ᵣ_)  (sym (invℝimpl x 0＃x)) (ℝ₊·
  (_ , 0<signᵣ x 0＃x 0<x)
  (_ , invℝ'-pos (absᵣ x) (0＃→0<abs x 0＃x)))

<ᵣ-·ᵣo : ∀ m n (o : ℝ₊) →  m <ᵣ n → (m ·ᵣ (fst o)) <ᵣ (n ·ᵣ (fst o))
<ᵣ-·ᵣo m n (o , 0<o) p =
  let z = subst (0 <ᵣ_) (·DistR+ n (-ᵣ m) o ∙
                   cong ((n ·ᵣ o) +ᵣ_) (-ᵣ· m o))
           (ℝ₊· (_ , x<y→0<y-x _ _ p) (o , 0<o))
  in 0<y-x→x<y _ _ z

<ᵣ-o·ᵣ : ∀ m n (o : ℝ₊) →  m <ᵣ n → ((fst o) ·ᵣ m) <ᵣ ((fst o) ·ᵣ n )
<ᵣ-o·ᵣ m n (o , 0<o) p =
  subst2 (_<ᵣ_)
    (·ᵣComm _ _) (·ᵣComm _ _) (<ᵣ-·ᵣo m n (o , 0<o) p)



<ᵣ₊Monotone·ᵣ : ∀ m n o s → (0 ≤ᵣ m) → (0 ≤ᵣ o)
       → m <ᵣ n → o <ᵣ s
       → (m ·ᵣ o) <ᵣ (n ·ᵣ s)
<ᵣ₊Monotone·ᵣ m n o s 0≤m 0≤o = PT.map2
   (λ m<n@((q , q') , m≤q , q<q' , q'≤n) →
        λ ((r , r') , o≤r , r<r' , r'≤s) →
    let 0≤q = isTrans≤ᵣ _ _ _ 0≤m m≤q
        0≤r = isTrans≤ᵣ _ _ _ 0≤o o≤r
        0≤r' = isTrans≤ᵣ _ _ _ 0≤r (≤ℚ→≤ᵣ _ _ (ℚ.<Weaken≤ _ _ r<r'))
        0≤n = isTrans≤ᵣ _ _ _ 0≤m (<ᵣWeaken≤ᵣ _ _ ∣ m<n ∣₁)
     in (q ℚ.· r , q' ℚ.· r') ,
           subst (m ·ᵣ o ≤ᵣ_) (sym (rat·ᵣrat _ _))
              (≤ᵣ₊Monotone·ᵣ m (rat q) o (rat r)
               (0≤q) 0≤o m≤q o≤r) ,
                ℚ.<Monotone·-onPos _ _ _ _
                  q<q' r<r' (≤ᵣ→≤ℚ _ _ 0≤q)
                            (≤ᵣ→≤ℚ _ _ 0≤r) ,
                (subst (_≤ᵣ n ·ᵣ s ) (sym (rat·ᵣrat _ _))
                  (≤ᵣ₊Monotone·ᵣ (rat q') n (rat r') s
                    0≤n 0≤r'
                    q'≤n r'≤s)))



/nᵣ-L : (n : ℕ₊₁) → Σ _ (Lipschitz-ℝ→ℝ _)
/nᵣ-L n = (fromLipschitz ([ 1 / n ] , _)
  (_ , Lipschitz-rat∘ ([ 1 / n ] , _) (ℚ._· [ 1 / n ])
   λ q r ε x →
     subst (ℚ._< ([ 1 / n ]) ℚ.· (fst ε))
      (sym (ℚ.pos·abs [ 1 / n ] (q ℚ.- r)
       (ℚ.<Weaken≤ 0 [ 1 / n ]
           ( (ℚ.0<→< [ 1 / n ] _))))
       ∙ cong ℚ.abs (ℚ.·Comm _ _ ∙ ℚ.·DistR+ q (ℚ.- r) [ 1 / n ]
        ∙ cong ((q ℚ.· [ 1 / n ]) ℚ.+_)
            (sym (ℚ.·Assoc -1 r [ 1 / n ]))))
      (ℚ.<-o· (ℚ.abs (q ℚ.- r)) (fst ε) [ 1 / n ]
       ((ℚ.0<→< [ 1 / n ] _))
       x)))

/nᵣ : ℕ₊₁ → ℝ → ℝ
/nᵣ = fst ∘ /nᵣ-L

/nᵣ-／ᵣ : ∀ n x (p : 0 ＃ fromNat (ℕ₊₁→ℕ n))
            → /nᵣ n x ≡ (x ／ᵣ[ fromNat (ℕ₊₁→ℕ n) , p ] )
/nᵣ-／ᵣ n x p = ≡Continuous _ _
  (Lipschitz→IsContinuous _ (fst (/nᵣ-L n)) (snd (/nᵣ-L n)))
   (IsContinuous·ᵣR _)
  (λ r → cong rat (cong (r ℚ.·_) (cong [ 1 /_] (sym (·₊₁-identityˡ _))))
    ∙ rat·ᵣrat _ _ ∙
      cong (rat r ·ᵣ_) (sym (invℝ-rat _ _ (fst (rat＃ _ _) p)) )) x

/nᵣ-pos : ∀ n x → 0 <ᵣ x → 0 <ᵣ /nᵣ n x
/nᵣ-pos n x 0<x = subst (0 <ᵣ_) (sym (/nᵣ-／ᵣ _ _ _))
                     (ℝ₊· (_ , 0<x) (_ , invℝ-pos _
                         (<ℚ→<ᵣ _ _ (ℚ.0<→< _ tt))))

seqSumUpTo : (ℕ → ℝ) → ℕ →  ℝ
seqSumUpTo s zero = 0
seqSumUpTo s (suc n) = s zero +ᵣ seqSumUpTo (s ∘ suc) n

seqSumUpTo· : ∀ s r n → seqSumUpTo s n ·ᵣ r ≡ seqSumUpTo ((_·ᵣ r) ∘ s) n
seqSumUpTo· s r zero = 𝐑'.0LeftAnnihilates r
seqSumUpTo· s r (suc n) =
  ·DistR+ (s zero) (seqSumUpTo (s ∘ suc) n) r ∙
   cong ((s zero ·ᵣ r) +ᵣ_) (seqSumUpTo· (s ∘ suc) r n)



seqSumUpTo' : (ℕ → ℝ) → ℕ →  ℝ
seqSumUpTo' s zero = 0
seqSumUpTo' s (suc n) = seqSumUpTo' s n +ᵣ s n

seqΣ : Seq → Seq
seqΣ = seqSumUpTo'

seqΣ' : Seq → Seq
seqΣ' = seqSumUpTo


seqSumUpTo-suc : ∀ f n → seqSumUpTo f n +ᵣ f n ≡
      f zero +ᵣ seqSumUpTo (λ x → f (suc x)) n
seqSumUpTo-suc f zero = +ᵣComm _ _
seqSumUpTo-suc f (suc n) =
  sym (+ᵣAssoc _ _ _) ∙
    cong ((f zero) +ᵣ_ ) (seqSumUpTo-suc _ _)

seqSumUpTo≡seqSumUpTo' : ∀ f n → seqSumUpTo' f n ≡ seqSumUpTo f n
seqSumUpTo≡seqSumUpTo' f zero = refl
seqSumUpTo≡seqSumUpTo' f (suc n) =
 cong (_+ᵣ (f n)) (seqSumUpTo≡seqSumUpTo' (f) n) ∙
   seqSumUpTo-suc f n

<-·sk-cancel : ∀ {m n k} → m ℕ.· suc k ℕ.< n ℕ.· suc k → m ℕ.< n
<-·sk-cancel {n = zero} x = ⊥.rec (ℕ.¬-<-zero x)
<-·sk-cancel {zero} {n = suc n} x = ℕ.suc-≤-suc (ℕ.zero-≤ {n})
<-·sk-cancel {suc m} {n = suc n} {k} x =
  ℕ.suc-≤-suc {suc m} {n}
    (<-·sk-cancel {m} {n} {k}
     (ℕ.≤-k+-cancel (subst (ℕ._≤ (k ℕ.+ n ℕ.· suc k))
       (sym (ℕ.+-suc _ _)) (ℕ.pred-≤-pred x))))

2≤x→1<quotient[x/2] : ∀ n → 0 ℕ.< (ℕ.quotient (2 ℕ.+ n) / 2)
2≤x→1<quotient[x/2] n =
 let z : 0 ℕ.<
             ((ℕ.quotient (2 ℕ.+ n) / 2) ℕ.· 2)
     z = subst (0 ℕ.<_) (ℕ.·-comm _ _)
          (ℕ.≤<-trans ℕ.zero-≤ (ℕ.<-k+-cancel (subst (ℕ._< 2 ℕ.+
             (2 ℕ.· (ℕ.quotient (2 ℕ.+ n) / 2)))
           (ℕ.≡remainder+quotient 2 (2 ℕ.+ n))
             (ℕ.<-+k {k = 2 ℕ.· (ℕ.quotient (2 ℕ.+ n) / 2)}
              (ℕ.mod< 1 (2 ℕ.+ n))))))
 in <-·sk-cancel {0} {ℕ.quotient (2 ℕ.+ n) / 2 } {k = 1}
     z



open ℕ.Minimal

-- invFacℕ : ∀ n → Σ _ (Least (λ k → n ℕ.< 2 !))
-- invFacℕ = {!!}

log2ℕ : ∀ n → Σ _ (Least (λ k → n ℕ.< 2 ^ k))
log2ℕ n = w n n ℕ.≤-refl
 where

  w : ∀ N n → n ℕ.≤ N
          → Σ _ (Least (λ k → n ℕ.< 2 ^ k))
  w N zero x = 0 , (ℕ.≤-refl , λ k' q → ⊥.rec (ℕ.¬-<-zero q))
  w N (suc zero) x = 1 , (ℕ.≤-refl ,
     λ { zero q → ℕ.<-asym (ℕ.suc-≤-suc ℕ.≤-refl)
      ; (suc k') q → ⊥.rec (ℕ.¬-<-zero (ℕ.pred-≤-pred q))})
  w zero (suc (suc n)) x = ⊥.rec (ℕ.¬-<-zero x)
  w (suc N) (suc (suc n)) x =
   let (k , (X , Lst)) = w N
          (ℕ.quotient 2 ℕ.+ n / 2)
          (ℕ.≤-trans (ℕ.pred-≤-pred (ℕ.2≤x→quotient[x/2]<x n))
             (ℕ.pred-≤-pred x))
       z = ℕ.≡remainder+quotient 2 (2 ℕ.+ n)
       zz = ℕ.<-+-≤ X X
       zzz : suc (suc n) ℕ.< (2 ^ suc k)
       zzz = subst2 (ℕ._<_)
           (ℕ.+-comm _ _
              ∙ sym (ℕ.+-assoc ((ℕ.remainder 2 ℕ.+ n / 2)) _ _)
               ∙ cong ((ℕ.remainder 2 ℕ.+ n / 2) ℕ.+_)
             ((cong ((ℕ.quotient 2 ℕ.+ n / 2) ℕ.+_)
              (sym (ℕ.+-zero (ℕ.quotient 2 ℕ.+ n / 2)))))
             ∙ z)
           (cong ((2 ^ k) ℕ.+_) (sym (ℕ.+-zero (2 ^ k))))
           (ℕ.≤<-trans
             (ℕ.≤-k+ (ℕ.≤-+k (ℕ.pred-≤-pred (ℕ.mod< 1 (2 ℕ.+ n))))) zz)
   in (suc k)
       , zzz
        , λ { zero 0'<sk 2+n<2^0' →
                ⊥.rec (ℕ.¬-<-zero (ℕ.pred-≤-pred 2+n<2^0'))
            ; (suc k') k'<sk 2+n<2^k' →
               Lst k' (ℕ.pred-≤-pred k'<sk)
                (<-·sk-cancel {k = 1}
                    (subst2 ℕ._<_ (ℕ.·-comm _ _) (ℕ.·-comm _ _)
                      (ℕ.≤<-trans (_ , z)
                         2+n<2^k' )))}





0<x^ⁿ : ∀ x n → 0 <ᵣ x → 0 <ᵣ (x ^ⁿ n)
0<x^ⁿ x zero x₁ = <ℚ→<ᵣ _ _ (𝟚.toWitness {Q = ℚ.<Dec 0 1} tt)
0<x^ⁿ x (suc n) x₁ = ℝ₊· (_ , 0<x^ⁿ x n x₁) (_ , x₁)


geometricProgression : ℝ → ℝ → ℕ → ℝ
geometricProgression a r zero = a
geometricProgression a r (suc n) =
  (geometricProgression a r n) ·ᵣ r

geometricProgressionClosed : ∀ a r n →
 geometricProgression a r n ≡ a ·ᵣ (r ^ⁿ n)
geometricProgressionClosed a r zero = sym (·IdR a)
geometricProgressionClosed a r (suc n) =
  cong (_·ᵣ r) (geometricProgressionClosed a r n) ∙
   sym (·ᵣAssoc _ _ _)

geometricProgression-suc : ∀ a r n →
   geometricProgression a r (suc n) ≡
    geometricProgression (a ·ᵣ r) r n
geometricProgression-suc a r zero = refl
geometricProgression-suc a r (suc n) =
  cong (_·ᵣ r) (geometricProgression-suc a r n)


geometricProgression-suc' : ∀ a r n →
   geometricProgression a r (suc n) ≡
    geometricProgression (a) r n  ·ᵣ r
geometricProgression-suc' a r _ = refl

Sₙ : ℝ → ℝ → ℕ → ℝ
Sₙ a r = seqSumUpTo (geometricProgression a r)


Sₙ-suc : ∀ a r n → Sₙ a r (suc n) ≡ (a +ᵣ (Sₙ a r n ·ᵣ r ))
Sₙ-suc a r n = cong (a +ᵣ_) (sym (seqSumUpTo· (geometricProgression a r) r n) )


SₙLem' : ∀ a n r → (Sₙ a r n) ·ᵣ (1 +ᵣ (-ᵣ r))  ≡
                   a ·ᵣ (1 +ᵣ (-ᵣ (r ^ⁿ n)))
SₙLem' a n r =
 let z : Sₙ a r n +ᵣ geometricProgression a r n
            ≡ (a +ᵣ (Sₙ a r n ·ᵣ r))
     z = cong (_+ᵣ (geometricProgression a r n))
           (sym (seqSumUpTo≡seqSumUpTo' (geometricProgression a r) n))
            ∙∙ seqSumUpTo≡seqSumUpTo' (geometricProgression a r) _
          ∙∙ Sₙ-suc a r n
     z' = ((sym (+IdR _) ∙ cong ((Sₙ a r n +ᵣ (-ᵣ (Sₙ a r n ·ᵣ r))) +ᵣ_)
             (sym (+-ᵣ (geometricProgression a r n))))
           ∙ 𝐑'.+ShufflePairs _ _ _ _ )
         ∙∙ cong₂ _+ᵣ_ z (
           (+ᵣComm (-ᵣ (Sₙ a r n ·ᵣ r))
              (-ᵣ (geometricProgression a r n)))) ∙∙
            (𝐑'.+ShufflePairs _ _ _ _ ∙
              cong ((a +ᵣ (-ᵣ (geometricProgression a r n))) +ᵣ_)
             ( (+-ᵣ (Sₙ a r n ·ᵣ r))) ∙ +IdR _)
 in (·DistL+ (Sₙ a r n) 1 (-ᵣ r)
      ∙ cong₂ _+ᵣ_ (·IdR (Sₙ a r n)) (𝐑'.-DistR· (Sₙ a r n) r))
      ∙∙ z' ∙∙ (cong₂ _+ᵣ_ (sym (·IdR a))
       (cong (-ᵣ_) (geometricProgressionClosed a r n) ∙
        sym (𝐑'.-DistR· _ _))
     ∙ sym (·DistL+ a 1 (-ᵣ ((r ^ⁿ (n))))))

SₙLem : ∀ a r (0＃1-r : 0 ＃ (1 +ᵣ (-ᵣ r))) n →
              (Sₙ a r n)   ≡
                   a ·ᵣ ((1 +ᵣ (-ᵣ (r ^ⁿ n)))
                     ／ᵣ[ (1 +ᵣ (-ᵣ r)) , 0＃1-r ])
SₙLem a r 0＃1-r n =
     x·y≡z→x≡z/y (Sₙ a r n)
       (a ·ᵣ (1 +ᵣ (-ᵣ (r ^ⁿ n))))
        _ 0＃1-r (SₙLem' a n r)
      ∙ sym (·ᵣAssoc _ _ _)

Sₙ-sup : ∀ a r n → (0 <ᵣ a) → (0 <ᵣ r) → (r<1 : r <ᵣ 1) →
                (Sₙ a r n)
                <ᵣ (a ·ᵣ (invℝ (1 +ᵣ (-ᵣ r)) (inl (x<y→0<y-x _ _ r<1))))
Sₙ-sup a r n a<0 0<r r<1  =
   isTrans≤<ᵣ _ _ _ (≡ᵣWeaken≤ᵣ _ _ (SₙLem a r _ n))
     (<ᵣ-o·ᵣ _ _ (a , a<0)
      (isTrans<≤ᵣ _ _ _
          (<ᵣ-·ᵣo (1 +ᵣ (-ᵣ (r ^ⁿ n))) 1
            (invℝ (1 +ᵣ (-ᵣ r)) (inl (x<y→0<y-x _ _ r<1)) ,
              0<1/x _ _ (( (x<y→0<y-x _ _ r<1))))
            (isTrans<≤ᵣ _ _ _
               (<ᵣ-o+ _ _ 1 (-ᵣ<ᵣ 0 (r ^ⁿ n) (0<x^ⁿ r n 0<r)))
               (≡ᵣWeaken≤ᵣ _ _ (+IdR _)) ))
          (≡ᵣWeaken≤ᵣ _ _ (·IdL _ ) )))

Seq<→Σ< : (s s' : Seq) →
  (∀ n → s n <ᵣ s' n) →
   ∀ n → seqSumUpTo s (suc n) <ᵣ seqSumUpTo s' (suc n)
Seq<→Σ< s s' x zero = subst2 _<ᵣ_
  (sym (+IdR _)) (sym (+IdR _)) (x 0)
Seq<→Σ< s s' x (suc n) = <ᵣMonotone+ᵣ _ _ _ _
 (x 0) (Seq<→Σ< (s ∘ suc) (s' ∘ suc) (x ∘ suc) n)

Seq≤→Σ≤ : (s s' : Seq) →
  (∀ n → s n ≤ᵣ s' n) →
   ∀ n → seqSumUpTo s n ≤ᵣ seqSumUpTo s' n
Seq≤→Σ≤ s s' x zero = ≤ᵣ-refl _
Seq≤→Σ≤ s s' x (suc n) = ≤ᵣMonotone+ᵣ _ _ _ _
 (x 0) (Seq≤→Σ≤ (s ∘ suc) (s' ∘ suc) (x ∘ suc) n)

Seq'≤→Σ≤ : (s s' : Seq) →
  (∀ n → s n ≤ᵣ s' n) →
   ∀ n → seqSumUpTo' s n ≤ᵣ seqSumUpTo' s' n
Seq'≤→Σ≤ s s' x zero = ≤ᵣ-refl _
Seq'≤→Σ≤ s s' x (suc n) =
 ≤ᵣMonotone+ᵣ _ _ _ _
 (Seq'≤→Σ≤ s s' x n)  (x n)

0≤seqΣ : ∀ s → (∀ n → 0 ≤ᵣ s n)
            → ∀ n → 0 ≤ᵣ seqΣ s n
0≤seqΣ s x zero = ≤ᵣ-refl _
0≤seqΣ s x (suc n) =
  ≤ᵣMonotone+ᵣ _ _ _ _ (0≤seqΣ s x n) (x n)

seriesDiff : (s : Seq)  →
  ∀ N n → (seqΣ s (n ℕ.+ N) +ᵣ (-ᵣ seqΣ s N)) ≡
     seqΣ (s ∘ (ℕ._+ N)) n
seriesDiff s N zero = +-ᵣ (seqΣ s N)
seriesDiff s N (suc n) =
  cong (_+ᵣ _) (+ᵣComm _ _) ∙∙
  sym (+ᵣAssoc _ _ _) ∙∙
   cong (s (n ℕ.+ N) +ᵣ_) (seriesDiff s N n)
    ∙ +ᵣComm (s (n ℕ.+ N)) (seqΣ (s ∘ (ℕ._+ N)) n)


IsCauchySequence : Seq → Type
IsCauchySequence s =
  ∀ (ε : ℝ₊) → Σ[ N ∈ ℕ ] (∀ m n → N ℕ.< n → N ℕ.< m →
    absᵣ ((s n) +ᵣ (-ᵣ (s m))) <ᵣ fst ε   )

IsCauchySequence' : Seq → Type
IsCauchySequence' s =
  ∀ (ε : ℚ₊) → Σ[ N ∈ ℕ ] (∀ m n → N ℕ.< n → N ℕ.< m →
    absᵣ ((s n) +ᵣ (-ᵣ (s m))) <ᵣ rat (fst ε)   )


IsConvSeries : Seq → Type
IsConvSeries s =
    ∀ (ε : ℝ₊) →
     Σ[ N ∈ ℕ ] ∀ n m →
       absᵣ (seqΣ (s ∘ (ℕ._+ (n ℕ.+ (suc N)))) m) <ᵣ fst ε

IsConvSeries' : Seq → Type
IsConvSeries' s =
    ∀ (ε : ℚ₊) →
     Σ[ N ∈ ℕ ] ∀ n m →
       absᵣ (seqΣ (s ∘ (ℕ._+ (n ℕ.+ (suc N)))) m) <ᵣ rat (fst ε)


IsoIsConvSeriesIsCauchySequenceSum : (s : Seq) →
  Iso (IsConvSeries s) (IsCauchySequence (seqΣ s))
IsoIsConvSeriesIsCauchySequenceSum s =
   codomainIsoDep λ ε →
     Σ-cong-iso-snd λ N →
        isProp→Iso (isPropΠ2 λ _ _ → squash₁)
         (isPropΠ4 λ _ _ _ _ → squash₁ )
         (λ f → ℕ.elimBy≤
           (λ n n' X <n <n' → subst (_<ᵣ fst ε)
             (minusComm-absᵣ _ _) (X <n' <n))
           λ n n' n≤n' N<n' N<n →
              subst ((_<ᵣ fst ε) ∘ absᵣ)
                 (cong (λ x → seqΣ (s ∘ (ℕ._+ x)) (n' ∸ n))
                    (ℕ.[n-m]+m (suc N) n N<n)
                   ∙∙ sym (seriesDiff s n (n' ∸ n)) ∙∙
                   cong (_+ᵣ (-ᵣ seqΣ s n))
                     (cong (seqΣ s)
                       (ℕ.[n-m]+m n n' n≤n')))
                 (f (n ∸ (suc N)) (n' ∸ n)))
         λ f n m →
           subst ((_<ᵣ fst ε) ∘ absᵣ)
             (seriesDiff s (n ℕ.+ suc N) m)
               (f (n ℕ.+ (suc N)) (m ℕ.+ (n ℕ.+ suc N))
               (subst (N ℕ.<_) (sym (ℕ.+-assoc _ _ _))
                 (ℕ.≤SumRight {suc N} {m ℕ.+ n}))
               (ℕ.≤SumRight {suc N} {n}))


IsConvSeries≃IsCauchySequenceSum : (s : Seq) →
  IsConvSeries s ≃ IsCauchySequence (seqΣ s)
IsConvSeries≃IsCauchySequenceSum s =
  isoToEquiv (IsoIsConvSeriesIsCauchySequenceSum s)

IsoIsConvSeries'IsCauchySequenceSum' : (s : Seq) →
  Iso (IsConvSeries' s) (IsCauchySequence' (seqΣ s))
IsoIsConvSeries'IsCauchySequenceSum' s =
 codomainIsoDep λ ε →
     Σ-cong-iso-snd λ N →
        isProp→Iso (isPropΠ2 λ _ _ → squash₁)
         (isPropΠ4 λ _ _ _ _ → squash₁ )

         (λ f → ℕ.elimBy≤
           (λ n n' X <n <n' → subst (_<ᵣ rat (fst ε))
             (minusComm-absᵣ _ _) (X <n' <n))
           λ n n' n≤n' N<n' N<n →
              subst ((_<ᵣ rat (fst ε)) ∘ absᵣ)
                 (cong (λ x → seqΣ (s ∘ (ℕ._+ x)) (n' ∸ n))
                    (ℕ.[n-m]+m (suc N) n N<n)
                   ∙∙ sym (seriesDiff s n (n' ∸ n)) ∙∙
                   cong (_+ᵣ (-ᵣ seqΣ s n))
                     (cong (seqΣ s)
                       (ℕ.[n-m]+m n n' n≤n')))
                 (f (n ∸ (suc N)) (n' ∸ n)))
         λ f n m →
           subst ((_<ᵣ rat (fst ε)) ∘ absᵣ)
             (seriesDiff s (n ℕ.+ suc N) m)
               (f (n ℕ.+ (suc N)) (m ℕ.+ (n ℕ.+ suc N))
               (subst (N ℕ.<_) (sym (ℕ.+-assoc _ _ _))
                 (ℕ.≤SumRight {suc N} {m ℕ.+ n}))
               (ℕ.≤SumRight {suc N} {n}))


IsConvSeries'≃IsCauchySequence'Sum : (s : Seq) →
  IsConvSeries' s ≃ IsCauchySequence' (seqΣ s)
IsConvSeries'≃IsCauchySequence'Sum s =
  isoToEquiv (IsoIsConvSeries'IsCauchySequenceSum' s)

isCauchyAprox : (ℚ₊ → ℝ) → Type
isCauchyAprox f = (δ ε : ℚ₊) →
  (absᵣ (f δ +ᵣ (-ᵣ  f ε)) <ᵣ rat (fst (δ ℚ₊+ ε)))

lim' : ∀ x → isCauchyAprox x → ℝ
lim' x y = lim x λ δ ε  → (invEq (∼≃abs<ε _ _ _)) (y δ ε)

-- HoTT 11.3.49

fromCauchySequence : ∀ s → IsCauchySequence s → ℝ
fromCauchySequence s ics =
  lim x y

 where
 x : ℚ₊ → ℝ
 x q = s (suc (fst (ics (ℚ₊→ℝ₊ q))))

 y : (δ ε : ℚ₊) → x δ ∼[ δ ℚ₊+ ε ] x ε
 y δ ε = invEq (∼≃abs<ε _ _ _)
    (ww (ℕ.Dichotomyℕ δₙ εₙ) )
  where
  δₙ = fst (ics (ℚ₊→ℝ₊ δ))
  εₙ = fst (ics (ℚ₊→ℝ₊ ε))

  ww : _ ⊎ _ → absᵣ (x δ +ᵣ (-ᵣ x ε)) <ᵣ rat (fst (δ ℚ₊+ ε))
  ww (inl δₙ≤εₙ) =
   let z = snd (ics (ℚ₊→ℝ₊ δ)) (suc εₙ) (suc δₙ)
              ℕ.≤-refl  (ℕ.suc-≤-suc δₙ≤εₙ )
   in isTrans<ᵣ (absᵣ (x δ +ᵣ (-ᵣ x ε)))
           (rat (fst (δ))) (rat (fst (δ ℚ₊+ ε)))
           z (<ℚ→<ᵣ _ _ (ℚ.<+ℚ₊' (fst δ) (fst δ) ε (ℚ.isRefl≤ (fst δ))))
  ww (inr εₙ<δₙ) =
    let z = snd (ics (ℚ₊→ℝ₊ ε)) (suc εₙ) (suc δₙ)
               (ℕ.≤-suc εₙ<δₙ) ℕ.≤-refl
    in isTrans<ᵣ (absᵣ (x δ +ᵣ (-ᵣ x ε)))
           (rat (fst (ε))) (rat (fst (δ ℚ₊+ ε)))
           z ((<ℚ→<ᵣ _ _
               (subst ((fst ε) ℚ.<_) (ℚ.+Comm _ _)
               (ℚ.<+ℚ₊' (fst ε) (fst ε) δ (ℚ.isRefl≤ (fst ε))))))


-- TODO HoTT 11.3.50.

fromCauchySequence' : ∀ s → IsCauchySequence' s → ℝ
fromCauchySequence' s ics =
  lim x y

 where
 x : ℚ₊ → ℝ
 x q = s (suc (fst (ics q)))

 y : (δ ε : ℚ₊) → x δ ∼[ δ ℚ₊+ ε ] x ε
 y δ ε = invEq (∼≃abs<ε _ _ _)
    (ww (ℕ.Dichotomyℕ δₙ εₙ) )
  where
  δₙ = fst (ics δ)
  εₙ = fst (ics ε)

  ww : _ ⊎ _ → absᵣ (x δ +ᵣ (-ᵣ x ε)) <ᵣ rat (fst (δ ℚ₊+ ε))
  ww (inl δₙ≤εₙ) =
   let z = snd (ics δ) (suc εₙ) (suc δₙ)
              ℕ.≤-refl  (ℕ.suc-≤-suc δₙ≤εₙ )
   in isTrans<ᵣ (absᵣ (x δ +ᵣ (-ᵣ x ε)))
           (rat (fst (δ))) (rat (fst (δ ℚ₊+ ε)))
           z (<ℚ→<ᵣ _ _ (ℚ.<+ℚ₊' (fst δ) (fst δ) ε (ℚ.isRefl≤ (fst δ))))
  ww (inr εₙ<δₙ) =
    let z = snd (ics ε) (suc εₙ) (suc δₙ)
               (ℕ.≤-suc εₙ<δₙ) ℕ.≤-refl
    in isTrans<ᵣ (absᵣ (x δ +ᵣ (-ᵣ x ε)))
           (rat (fst (ε))) (rat (fst (δ ℚ₊+ ε)))
           z ((<ℚ→<ᵣ _ _
               (subst ((fst ε) ℚ.<_) (ℚ.+Comm _ _)
               (ℚ.<+ℚ₊' (fst ε) (fst ε) δ (ℚ.isRefl≤ (fst ε))))))


limₙ→∞_is_ : Seq → ℝ → Type
limₙ→∞ s is x =
  ∀ (ε : ℝ₊) → Σ[ N ∈ ℕ ]
    (∀ n → N ℕ.< n →
      absᵣ ((s n) +ᵣ (-ᵣ x)) <ᵣ (fst ε))

lim'ₙ→∞_is_ : Seq → ℝ → Type
lim'ₙ→∞ s is x =
  ∀ (ε : ℚ₊) → Σ[ N ∈ ℕ ]
    (∀ n → N ℕ.< n →
      absᵣ ((s n) +ᵣ (-ᵣ x)) <ᵣ (rat (fst ε)))



Limₙ→∞ : Seq → Type
Limₙ→∞ s = Σ _ (limₙ→∞ s is_)


ε<2ⁿ : (ε : ℚ₊) → Σ[ n ∈ ℕ ] fst ε ℚ.< 2 ℚ^ⁿ n
ε<2ⁿ ε = let n = fst (log2ℕ (fst (ℚ.ceilℚ₊ ε))) in n ,
         subst (fst ε ℚ.<_) (sym (ℚ.fromNat-^ _ _))
          (ℚ.isTrans< _ _ (fromNat (2 ^ n))
                  ((snd (ℚ.ceilℚ₊ ε)))
                   (ℚ.<ℤ→<ℚ (ℤ.pos ((fst (ℚ.ceilℚ₊ ε))))
                     _ (ℤ.ℕ≤→pos-≤-pos  _ _
                    (fst (snd (log2ℕ (fst (ℚ.ceilℚ₊ ε))))))))


1/2ⁿ<ε : (ε : ℚ₊) → Σ[ n ∈ ℕ ] [ 1 / 2 ] ℚ^ⁿ n ℚ.< fst ε
1/2ⁿ<ε ε =
 let (n , 1/ε<n) = ε<2ⁿ (invℚ₊ ε)
 in n , invEq (ℚ.invℚ₊-<-invℚ₊ (([ 1 / 2 ] , _) ℚ₊^ⁿ n) ε)
         (subst (fst (invℚ₊ ε) ℚ.<_)
           (sym (ℚ.invℚ₊-ℚ^ⁿ ([ 1 / 2 ] , _) n)) 1/ε<n)



ratio→seqLimit : ∀ (s : Seq) → (∀ n → Σ[ r ∈ ℚ ] (s n ≡ rat r))
  → (sPos : ∀ n → rat 0 <ᵣ (s n))
  → lim'ₙ→∞ (λ n →  s (suc n) ／ᵣ[ s n , inl ((sPos n)) ]) is 0
  → lim'ₙ→∞ s is 0
ratio→seqLimit s sRat sPos l (ε , 0<ε) =
 (uncurry w)
    (l ([ 1 / 2 ] , _))

 where
 w : ∀ N → ((n : ℕ) →  N ℕ.< n →
          absᵣ ((s (suc n) ／ᵣ[ s n , inl (sPos n) ]) +ᵣ (-ᵣ 0)) <ᵣ
          rat [ 1 / 2 ]) →
       Σ ℕ (λ N → (n : ℕ) → N ℕ.< n → absᵣ (s n +ᵣ (-ᵣ 0)) <ᵣ rat ε)
 w N f =
     let 0<s' = ((subst (0 <ᵣ_) (snd (sRat (suc N))))
                   (sPos (suc N)))
         δ₊ = (ε , 0<ε) ℚ₊· invℚ₊ (fst (sRat (suc N)) ,
                 (ℚ.<→0< _  (<ᵣ→<ℚ 0 _
                   0<s')))
         (m½ , q) = 1/2ⁿ<ε δ₊
         pp : rat ([ 1 / 2 ] ℚ^ⁿ m½)  <ᵣ
                 ((rat ε ·ᵣ invℝ (s (suc N)) (inl (sPos _))))
         pp = isTrans<≡ᵣ _ _ _ (<ℚ→<ᵣ _ _ q)
                 (rat·ᵣrat _ _ ∙
                   cong (rat ε ·ᵣ_)
                     (cong rat (sym (ℚ.invℚ₊≡invℚ _
                       (inl (<ᵣ→<ℚ 0 _ 0<s'))))
                       ∙ sym (invℝ-rat _ (inl 0<s') _) ∙
                       cong₂ invℝ (sym (snd (sRat (suc N))))
                         (isProp→PathP (λ i → isProp＃ _ _)  _ _)))
         pp' = subst ((rat ([ ℤ.pos 1 / 1+ 1 ] ℚ^ⁿ m½) ·ᵣ s (suc N)) <ᵣ_)
                  ([x/y]·yᵣ _ _ _) (<ᵣ-·ᵣo _ _ (s (suc N) , (sPos _)) pp)
         zzz : ∀ m → s (((suc (suc (m ℕ.+ m½))) ℕ.+ N))
                     ≤ᵣ
                      s (suc N) ·ᵣ  (rat ([ ℤ.pos 1 / 1+ 1 ] ℚ^ⁿ m½))
         zzz m  = isTrans≤ᵣ _ _ _ (g (m ℕ.+ m½))
                     (≤ᵣ-o·ᵣ _ _ (s (suc N)) (<ᵣWeaken≤ᵣ _ _ (sPos _))
                       (≤ℚ→≤ᵣ _ _ (subst2 ℚ._≤_ (ℚ.·-ℚ^ⁿ (suc m) m½ [ 1 / 2 ])
                           (ℚ.·IdL _)
                          (ℚ.≤-·o (([ ℤ.pos 1 / 1+ 1 ] ℚ^ⁿ (suc m)))
                               1 _ ((ℚ.0≤ℚ₊ (_ ℚ₊^ⁿ m½)))
                                  (ℚ.x^ⁿ≤1 [ ℤ.pos 1 / 1+ 1 ] (suc m)
                                    (𝟚.toWitness
                                       {Q = ℚ.≤Dec 0  [ ℤ.pos 1 / 1+ 1 ]} tt)
                                    (𝟚.toWitness
                                       {Q = ℚ.≤Dec [ ℤ.pos 1 / 1+ 1 ] 1} tt))
                                  ))) )
     in (1 ℕ.+ m½) ℕ.+ N ,
          λ m <m →
           isTrans≤<ᵣ _ _ _ (
               subst2 (_≤ᵣ_)
               (cong s ((cong (ℕ._+ N) (cong suc (sym (+-suc _ _))
                ∙ sym (+-suc _ _)) ∙ sym (ℕ.+-assoc _ _ N) )
                   ∙ snd <m) ∙ sym (absᵣPos _ (sPos _))
                 ∙ cong absᵣ (sym (+IdR (s m))) )
                 (·ᵣComm _ _)
                (zzz (fst <m)) --(zzz m <m)
                ) pp'
          --   (lowerℚBound (ε ·ᵣ invℝ (s (suc N)) (inl (sPos _)))
          -- (ℝ₊· (ε , 0<ε) (_ , invℝ-pos (s (suc N)) (sPos _))))
  where

   f' : ((n : ℕ) →  N ℕ.< n →
          (s (suc n)) <ᵣ
          s n ·ᵣ rat [ 1 / 2 ])
   f' n n< =
    subst2 _<ᵣ_
      ((congS (_·ᵣ s n) (+IdR _) ∙
        [x/y]·yᵣ _ _ _)) (·ᵣComm _ _)
     (<ᵣ-·ᵣo _ _ (s n , sPos _)
      (isTrans≤<ᵣ _ _ _ (≤absᵣ _) (f n n<)))

   g : ∀ m → s ((suc (suc m)) ℕ.+ N)
             ≤ᵣ (s (suc N)) ·ᵣ rat ([ 1 / 2 ] ℚ^ⁿ (suc m))
   g zero = subst (s (suc (suc N)) ≤ᵣ_)
                (cong ((s (suc N) ·ᵣ_) ∘ rat) (sym (ℚ.·IdR _)))
                 (<ᵣWeaken≤ᵣ _ _ (f' (suc N) (ℕ.≤-refl {suc N})))
   g (suc m) =
     isTrans≤ᵣ _ _ _ (<ᵣWeaken≤ᵣ _ _ (f' (2 ℕ.+ m ℕ.+ N)
      (subst (N ℕ.<_)
        (cong suc (ℕ.+-suc _ _)) (ℕ.≤SumRight {suc N} {suc m})))) ww
    where
    ww : (s (suc (suc m) ℕ.+ N) ·ᵣ rat [ 1 / 2 ]) ≤ᵣ
         (s (suc N) ·ᵣ rat ([ 1 / 2 ] ℚ^ⁿ suc (suc m)))

    ww =
       subst ((s (suc (suc m) ℕ.+ N) ·ᵣ rat [ 1 / 2 ]) ≤ᵣ_)

         (sym (·ᵣAssoc _ _ _) ∙
           cong (s (suc N) ·ᵣ_) (sym (rat·ᵣrat _ _)))
            (≤ᵣ-·o _ _ [ 1 / 2 ] (ℚ.decℚ≤? {0} {[ 1 / 2 ]}) (g m))


-- TODO : generalize properly
ratioTest₊ : ∀ (s : Seq) → (sPos : ∀ n → rat 0 <ᵣ (s n))
     → lim'ₙ→∞ s is 0
     → (lim'ₙ→∞ (λ n →  s (suc n) ／ᵣ[ s n , inl ((sPos n)) ]) is 0)
     → IsConvSeries' s
ratioTest₊ s sPos l' l ε₊@(ε , 0<ε) =
  N , ww

 where
 ½ᵣ = (ℚ₊→ℝ₊ ([ 1 / 2 ] , _))
 N½ = l ([ 1 / 2 ] , _)
 ε/2 : ℚ₊
 ε/2 = /2₊ ε₊

 Nε = (l' ε/2)

 N : ℕ
 N = suc (ℕ.max (suc (fst N½)) (fst Nε))

 ww : ∀ m n → absᵣ (seqΣ (λ x → s (x ℕ.+ (m ℕ.+ suc N))) n) <ᵣ (rat ε)
 ww m n = isTrans≤<ᵣ _ _ _
   (≡ᵣWeaken≤ᵣ _ _
     (absᵣNonNeg (seqΣ (λ x → s (x ℕ.+ (m ℕ.+ suc N))) n)
     (0≤seqΣ _ (λ n → <ᵣWeaken≤ᵣ _ _ (sPos (n ℕ.+ (m ℕ.+ suc N)))) _))) pp

  where
  s' : Seq
  s' = s ∘ (ℕ._+ (suc (m ℕ.+ N)))


  f' : ((n : ℕ) →  N ℕ.≤ n →
         (s (suc n)) ≤ᵣ
         s n ·ᵣ rat [ 1 / 2 ])
  f' n n< =
     subst2 {x = ((s (suc n) ／ᵣ[ s n , inl (sPos n) ])
                    +ᵣ 0 ) ·ᵣ s n }
        _≤ᵣ_ (congS (_·ᵣ s n) (+IdR _) ∙
          [x/y]·yᵣ _ _ _) (·ᵣComm _ _)
       ((<ᵣWeaken≤ᵣ _ _
          (<ᵣ-·ᵣo _ _ (s n , sPos _)
           (isTrans≤<ᵣ _ _ _ (≤absᵣ _)
             (snd N½ n (
              ℕ.<-trans (ℕ.left-≤-max {suc (fst N½)} {fst Nε})
               n<))))))


  p : ∀ n → s' n ≤ᵣ geometricProgression (s (m ℕ.+ N)) (fst ½ᵣ) n
  p zero =
     isTrans≤ᵣ _ _ _ ((f' (m ℕ.+ N) (ℕ.≤SumRight {N} {m}) ))
             (subst ((s (m ℕ.+ N) ·ᵣ rat [ ℤ.pos 1 / 1+ 1 ]) ≤ᵣ_)
                (·IdR _)
                 (≤ᵣ-o·ᵣ (fst ½ᵣ) 1 (s (m ℕ.+ N))
                   (<ᵣWeaken≤ᵣ _ _ (sPos _))
                  (≤ℚ→≤ᵣ _ _ ((𝟚.toWitness {Q = ℚ.≤Dec ([ 1 / 2 ]) 1} _)))))

  p (suc n) =
    isTrans≤ᵣ _ _ _ (f' _
      (subst (N ℕ.≤_) (sym (ℕ.+-assoc n (1 ℕ.+ m) N))
        ℕ.≤SumRight))
      (≤ᵣ-·o _ _ ([ 1 / 2 ]) ((𝟚.toWitness {Q = ℚ.≤Dec 0 ([ 1 / 2 ])} _)) (p n))

  p' = Seq'≤→Σ≤ s' (geometricProgression (s (m ℕ.+ N)) (fst ½ᵣ))
        p

  s<ε : (s (m ℕ.+ N)) <ᵣ rat (fst ε/2)
  s<ε = subst (_<ᵣ rat (fst ε/2)) (+IdR _)
           ((isTrans≤<ᵣ _ _ _
          (≤absᵣ ((s (m ℕ.+ N)) +ᵣ (-ᵣ 0))) (snd Nε _
           (ℕ.≤<-trans ℕ.right-≤-max ℕ.≤SumRight))))


  pp : (seqΣ (λ x → s (x ℕ.+ (m ℕ.+ suc N))) n) <ᵣ (rat ε)
  pp =
      subst {x = ℕ._+ suc (m ℕ.+ N) } {y = λ z → z ℕ.+ (m ℕ.+ suc N)}
           (λ h → seqΣ (s ∘S h) n <ᵣ rat ε)

          (funExt (λ x → cong (x ℕ.+_) (sym (ℕ.+-suc _ _)) ))
          (isTrans≤<ᵣ _ _ _ (p' n)
            (isTrans≤<ᵣ _ _ _
              (≡ᵣWeaken≤ᵣ _ _ (seqSumUpTo≡seqSumUpTo' _ _))
                (isTrans<≤ᵣ _ _ _
                 (Sₙ-sup (s (m ℕ.+ N)) (fst ½ᵣ)
                   n (sPos _) (snd ½ᵣ)
                    (<ℚ→<ᵣ _ _ ((𝟚.toWitness {Q = ℚ.<Dec [ 1 / 2 ] 1} tt))))
                (isTrans≤ᵣ _ _ _
                  (≤ᵣ₊Monotone·ᵣ _ _ _ 2
                        (<ᵣWeaken≤ᵣ _ _ (<ℚ→<ᵣ _ _ (ℚ.0<ℚ₊ ε/2)))
                          (<ᵣWeaken≤ᵣ _ _
                             ((0<1/x _ _ (
                       <ℚ→<ᵣ _ _
                       (𝟚.toWitness {Q = ℚ.<Dec 0 [ 1 / 2 ]} tt)))))

                    (<ᵣWeaken≤ᵣ _ _ s<ε)
                    (≡ᵣWeaken≤ᵣ _ _
                       (invℝ-rat _ _
                        (inl ((𝟚.toWitness {Q = ℚ.<Dec 0 [ 1 / 2 ]} tt))))))
                        (≡ᵣWeaken≤ᵣ _ _ (sym (rat·ᵣrat _  _) ∙
                          cong rat (sym (ℚ.·Assoc _ _ _) ∙
                            cong (ε ℚ.·_) ℚ.decℚ? ∙ ℚ.·IdR _)))

                        ))))


expSeq : ℝ → Seq
expSeq x zero = 1
expSeq x (suc n) = /nᵣ (1+ n) (expSeq x n ·ᵣ x)

expSeq-rat : ∀ (q : ℚ) → (n : ℕ) → Σ[ r ∈ ℚ ] (expSeq (rat q) n ≡ rat r)
expSeq-rat q zero = 1 , refl
expSeq-rat q (suc n) =
  let (e , p) = expSeq-rat q n
  in (e ℚ.· q)  ℚ.· [ 1 / (1+ n) ] ,
       cong (/nᵣ (1+ n)) (cong (_·ᵣ (rat q)) p ∙ sym (rat·ᵣrat _ _))

expSeries-rat : ∀ (q : ℚ) → (n : ℕ) →
  Σ[ r ∈ ℚ ] (seqΣ (expSeq (rat q)) n ≡ rat r)
expSeries-rat q zero = 0 , refl
expSeries-rat q (suc n) =
  let (e , p) = expSeries-rat q n
      (e' , p') = expSeq-rat q n
  in (e ℚ.+ e') , cong₂ _+ᵣ_ p p'

expSeqPos : ∀ x → 0 <ᵣ x → ∀ n → 0 <ᵣ expSeq x n
expSeqPos x 0<x zero = decℚ<ᵣ?
expSeqPos x 0<x (suc n) =
 /nᵣ-pos (1+ n) _ (ℝ₊· (_ , expSeqPos x 0<x n) (_ , 0<x))

limₙ→∞[expSeqRatio]=0 : ∀ x → ∀ (0<x : 0 ℚ.< x)  → lim'ₙ→∞
      (λ n →
         expSeq (rat x) (suc n) ／ᵣ[ expSeq (rat x) n ,
         inl (expSeqPos (rat x) (<ℚ→<ᵣ 0 x 0<x) n) ])
      is 0
limₙ→∞[expSeqRatio]=0 x 0<x =
  subst (lim'ₙ→∞_is 0)
    (funExt (w (rat x) _))
    w'

 where
 x₊ : ℚ₊
 x₊ = x , ℚ.<→0< _ 0<x

 0<ᵣx = <ℚ→<ᵣ 0 x 0<x
 w : ∀ x 0<x n → (x ·ᵣ rat ([ 1 / 1+ n ])) ≡ (expSeq x (suc n) ／ᵣ[ expSeq x n ,
                    inl (expSeqPos x 0<x n) ])
 w x 0<x zero = cong₂ {y = expSeq x 1} _·ᵣ_
        (( sym (·IdR x) ∙
        (cong
            (x ·ᵣ_) (sym (invℝ-rat _
              (invEq (rat＃ _ _) (inl (ℚ.decℚ<? {0} {1})))
               (inl (ℚ.decℚ<? {0} {1}))))) ∙ sym (/nᵣ-／ᵣ 1 (x)
          (invEq (rat＃ _ _) (inl (ℚ.decℚ<? {0} {1}))))
           ∙ (cong (/nᵣ 1) (sym (·IdL x))) ) )
     (sym (invℝ-rat 1 (inl ((expSeqPos x 0<x zero)))
            ((inl (ℚ.decℚ<? {0} {1})))))

 w x 0<x (suc n) =
   let z = _
       z' = _
   in ((cong (x ·ᵣ_) ((sym (·IdL _) ∙
         cong₂ _·ᵣ_ (sym (x·invℝ[x] _ _))
           (cong rat (sym (ℚ.fromNat-invℚ _
                (inl (ℚ.<ℤ→<ℚ _ _ (ℤ.suc-≤-suc ℤ.zero-≤pos )))))
             ∙ sym (invℝ-rat _ _ _)))
               ∙ sym (·ᵣAssoc _ _ _))
         ∙ ·ᵣAssoc _ (expSeq x (suc n)) _)
           ∙ cong₂ (_·ᵣ_) (·ᵣComm _ _) (·ᵣComm z' z))
       ∙ (·ᵣAssoc _ z z'
         ∙ cong (_／ᵣ[ expSeq x (suc n) ,
                    inl (expSeqPos x 0<x (suc n)) ])
                     (sym (/nᵣ-／ᵣ (2+ n) (/nᵣ (1+ n) (expSeq x n ·ᵣ x) ·ᵣ x)
                       (inl (<ℚ→<ᵣ 0 _ (ℚ.<ℤ→<ℚ _ _
                         (ℤ.suc-≤-suc ℤ.zero-≤pos )))))))

 w' : lim'ₙ→∞ _ is 0
 w' ε =
  let (cN , X) = ℚ.ceilℚ₊ (x₊ ℚ₊· (invℚ₊ ε))

      X'' = subst (ℚ._< [ pos cN / 1+ 0 ])
               (cong (x ℚ.·_) (sym (ℚ.invℚ₊≡invℚ ε _) ))
             X
      X' : x ℚ.· [ pos 1 / 1+ cN ] ℚ.< fst ε

      X' = subst (ℚ._< fst ε)
             ((cong (x ℚ.·_) (ℚ.fromNat-invℚ _ _)))
            (ℚ.ℚ-x/y<z→x/z<y x [ pos (suc cN) / 1 ] (fst ε)
                        0<x (ℚ.<ℤ→<ℚ _ _ (ℤ.suc-≤-suc ℤ.zero-≤pos))
                         (ℚ.0<→< _ (snd ε))
                         (ℚ.isTrans< _ [ pos (cN) / 1+ 0 ] _
                           X'' (ℚ.<ℤ→<ℚ _ _ ℤ.isRefl≤ )))
  in (suc cN) , (λ n' <n' →
      let 0<n' = ℚ.<ℤ→<ℚ _ _
             (ℤ.ℕ≤→pos-≤-pos _ _ (ℕ.suc-≤-suc ℕ.zero-≤))
      in isTrans≡<ᵣ _ _ _
          (cong absᵣ (+IdR _) ∙ absᵣPos _
            (ℝ₊· (_ , <ℚ→<ᵣ 0 x 0<x)
                       (_ ,
                          <ℚ→<ᵣ _ _
                           (ℚ.invℚ-pos [ pos (suc n') / 1 ]
                            (inl 0<n') 0<n')))
                             ∙ sym (rat·ᵣrat _ _))
           (<ℚ→<ᵣ _ _ (ℚ.isTrans< _ _ _
             (ℚ.<-o· [ 1 / 1+ n' ]
                     [ 1 / 1+ cN ] x 0<x
                      ((ℤ.ℕ≤→pos-≤-pos _ _ (ℕ.≤-suc <n'))))
                          X')))


limₙ→∞[expSeq]=0 : ∀ x → (0<x : 0 ℚ.< x) →  lim'ₙ→∞ expSeq (rat x) is 0
limₙ→∞[expSeq]=0 x 0<x =
  ratio→seqLimit _ (expSeq-rat x)
      (expSeqPos (rat x) _) (limₙ→∞[expSeqRatio]=0 x 0<x)


expSeriesConvergesAtℚ₊ : ∀ x → 0 ℚ.< x → IsConvSeries' (expSeq (rat x))
expSeriesConvergesAtℚ₊ x 0<x =
 ratioTest₊ (expSeq (rat x)) (expSeqPos (rat x) (<ℚ→<ᵣ _ _ 0<x))
      (limₙ→∞[expSeq]=0 x  0<x)
      (limₙ→∞[expSeqRatio]=0 x 0<x)

expℚ₊ : ℚ₊ → ℝ
expℚ₊ q = fromCauchySequence' _
  (fst (IsConvSeries'≃IsCauchySequence'Sum (expSeq (rat (fst q))))
    (expSeriesConvergesAtℚ₊ (fst q) (ℚ.0<ℚ₊ q)))


expSeriesVal : ℕ → ℚ
expSeriesVal n = fst (expSeries-rat 1 n)

𝑒 : ℝ
𝑒 = expℚ₊ 1

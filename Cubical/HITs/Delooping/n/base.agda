{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.HITs.Delooping.n.base where

open import Cubical.HITs.Susp
open import Cubical.HITs.Pushout
open import Cubical.Data.Nat
open import Cubical.Data.Fin
open import Cubical.Data.Nat.Order
open import Cubical.Foundations.Everything


open import Cubical.HITs.SetQuotients
open import Cubical.Relation.Nullary
open import Cubical.Data.Empty

open import Cubical.Data.Sigma
open import Cubical.Data.Sum

open import Cubical.Data.Empty renaming (rec to ⊥-rec)
open import Cubical.Induction.WellFounded
open import Cubical.Data.Nat.Divisibility


_mod_ : (x n : ℕ) → ℕ
x mod zero = 0
x mod (suc n) = (+induction n (λ _ → ℕ) (λ x _ → x) λ _ x → x) x

quotient_/suc_ : (x n : ℕ) → ℕ
quotient x /suc n = +induction n (λ _ → ℕ) (λ _ _ → 0) (λ _ → suc) x

ℕ→rem+quot-mod : (n x : ℕ) → ℕ × ℕ
ℕ→rem+quot-mod zero x = x , 0
ℕ→rem+quot-mod (suc n) x = (x mod (suc n)) , (quotient x /suc n)

rem+quot-mod≡ : (n x : ℕ) → fst (ℕ→rem+quot-mod n x) + n · snd (ℕ→rem+quot-mod n x) ≡ x
rem+quot-mod≡ zero x = +-comm x 0
rem+quot-mod≡ (suc n) = +induction n (λ x → fst (ℕ→rem+quot-mod (suc n) x) + (suc n) · snd (ℕ→rem+quot-mod (suc n) x) ≡ x)
                                     (λ x base → cong₂ _+_ (+inductionBase n (λ _ → ℕ) (λ x _ → x) (λ _ x → x) x base)
                                                            (cong ((suc n) ·_) (+inductionBase n (λ _ → ℕ) (λ _ _ → 0) (λ _ → suc) x base))
                                               ∙∙ cong (x +_) (·-comm n 0)
                                               ∙∙ +-comm x 0)
                                     λ x ind → cong₂ _+_ (+inductionStep n (λ _ → ℕ) (λ x _ → x) (λ _ x → x) x)
                                                          (cong ((suc n) ·_) (+inductionStep n (λ _ → ℕ) (λ _ _ → 0) (λ _ → suc) x))
                                            ∙∙ cong (+induction n (λ _ → ℕ) (λ x₁ _ → x₁) (λ _ x₁ → x₁) x +_)
                                                    (·-suc (suc n) (+induction n (λ _ → ℕ) (λ _ _ → 0) (λ _ → suc) x))
                                            ∙∙ cong (+induction n (λ _ → ℕ) (λ x₁ _ → x₁) (λ _ x₁ → x₁) x +_)
                                                    (+-comm (suc n) ((suc n) · (+induction n (λ _ → ℕ) (λ _ _ → 0) (λ _ → suc) x)))
                                            ∙∙ +-assoc (+induction n (λ _ → ℕ) (λ x₁ _ → x₁) (λ _ x₁ → x₁) x)
                                                       ((suc n) · +induction n (λ _ → ℕ) (λ _ _ → 0) (λ _ → suc) x)
                                                       (suc n)
                                            ∙∙ cong (_+ suc n) ind
                                             ∙ +-comm x (suc n)

mod< : (n x : ℕ) → x mod (suc n) < (suc n)
mod< n = +induction n (λ x → x mod (suc n) < suc n)
                      (λ x base → fst base , (cong (λ x → fst base + suc x) (+inductionBase n (λ _ → ℕ) (λ x _ → x) (λ _ x → x) x base) ∙ snd base))
                      λ x ind → fst ind , cong (λ x → fst ind + suc x) (+inductionStep n (λ _ → ℕ) (λ x _ → x) (λ _ x → x) x) ∙ snd ind

+mod : (n x : ℕ) → x mod n ≡ ((x + n) mod n)
+mod zero x = refl
+mod (suc n) x = sym (+inductionStep n (λ _ → ℕ) (λ x₁ _ → x₁) (λ _ x₁ → x₁) x)
               ∙ cong (+induction n (λ _ → ℕ) (λ x₁ _ → x₁) (λ _ x₁ → x₁)) (+-comm (suc n) x)

+mod' : (n x : ℕ) → x mod n ≡ ((n + x) mod n)
+mod' zero _ = refl
+mod' (suc n) x = sym (+inductionStep n (λ _ → ℕ) (λ x₁ _ → x₁) (λ _ x₁ → x₁) x)

mod-mod : (n x y : ℕ) → (x + y) mod n ≡ (((x mod n) + (y mod n)) mod n)
mod-mod zero _ _ = refl
mod-mod (suc n) = +induction n (λ z → (x : ℕ) → ((z + x) mod (suc n)) ≡ (((z mod (suc n)) + (x mod (suc n))) mod (suc n)))
                         (λ x p → +induction n _
                                     (λ y q → cong (+induction n (λ _ → ℕ) (λ x₁ _ → x₁) (λ _ x₁ → x₁))
                                                    (sym (cong₂  _+_ (+inductionBase n (λ _ → ℕ) (λ x _ → x) (λ _ x → x) x p)
                                                    (+inductionBase n (λ _ → ℕ) (λ x _ → x) (λ _ x → x) y q))))
                                     λ y ind → cong (+induction n (λ _ → ℕ) (λ x₁ _ → x₁) (λ _ x₁ → x₁)) (cong (x +_) (+-comm (suc n) y) ∙ (+-assoc x y (suc n)))
                                                  ∙∙ sym (+mod (suc n) (x + y))
                                                  ∙∙ ind
                                                   ∙ cong (λ z → +induction n (λ _ → ℕ) (λ x₁ _ → x₁) (λ _ x₁ → x₁)
                                                                 ((+induction n (λ _ → ℕ) (λ x₁ _ → x₁) (λ _ x₁ → x₁) x + z)))
                                                          (+mod (suc n) y ∙ cong (+induction n (λ _ → ℕ) (λ x₁ _ → x₁) (λ _ x₁ → x₁)) (+-comm y (suc n))))
                         λ x p y → cong (+induction n (λ _ → ℕ) (λ x₁ _ → x₁) (λ _ x₁ → x₁)) (cong suc (sym (+-assoc n x y)))
                                      ∙∙ sym (+mod' (suc n) (x + y))
                                      ∙∙ p y
                                       ∙ sym (cong (+induction n (λ _ → ℕ) (λ x₁ _ → x₁) (λ _ x₁ → x₁))
                                             (cong (_+ +induction n (λ _ → ℕ) (λ x₁ _ → x₁) (λ _ x₁ → x₁) y)
                                             (cong (+induction n (λ _ → ℕ) (λ x₁ _ → x₁) (λ _ x₁ → x₁))
                                             (+-comm (suc n) x) ∙ sym (+mod (suc n) x))))

modx2 : {n : ℕ} → (x : ℕ) → (x mod n) mod n ≡ x mod n
modx2 {n = zero} _ = refl
modx2 {n = suc n} =
  +induction n (λ x → (x mod suc n) mod (suc n) ≡ x mod (suc n))
             (λ x p → cong (_mod (suc n))
                            (+inductionBase n (λ _ → ℕ) (λ x₁ _ → x₁) (λ _ x₁ → x₁) x p))
              λ x p → cong (_mod (suc n))
                            (+inductionStep n (λ _ → ℕ) (λ x₁ _ → x₁) (λ _ x₁ → x₁) x)
                             ∙∙ p
                             ∙∙ +mod (suc n) x
                              ∙ (cong (_mod (suc n)) (+-comm x (suc n)))

modR : (n x y : ℕ) → (x + y) mod n ≡ (x + y mod n) mod n
modR zero x y = refl
modR (suc n) x =
  +induction n _
    (λ y p → cong (λ z → (x + z) mod (suc n)) (sym (+inductionBase n (λ _ → ℕ) (λ x₁ _ → x₁) (λ _ x₁ → x₁) y p)))
    λ y p → cong (_mod suc n) (+-assoc x (suc n) y
                            ∙∙ (cong (_+ y) (+-comm x (suc n)))
                            ∙∙ sym (+-assoc (suc n) x y))
         ∙∙ sym (+mod' (suc n) (x + y))
         ∙∙ (p ∙ cong (λ z → (x + z) mod suc n) (+mod' (suc n) y))

modL : (n x y : ℕ) → (x + y) mod n ≡ (x mod n + y) mod n
modL n x y = cong (_mod n) (+-comm x y) ∙∙ modR n y x ∙∙ cong (_mod n) (+-comm y (x mod n))

zero-charac : (n : ℕ) → n mod n ≡ 0
zero-charac zero = refl
zero-charac (suc n) = cong (_mod suc n) (+-comm 0 (suc n))
                  ∙∙ +inductionStep n (λ _ → ℕ) (λ x _ → x) (λ _ x → x) 0
                  ∙∙ +inductionBase n (λ _ → ℕ) (λ x _ → x) (λ _ x → x) 0 (n , (+-comm n 1))

_+/_ : {n : ℕ} → Fin (suc n) → Fin (suc n) → Fin (suc n)
_+/_ {n = n} x y = (((fst x) + (fst y)) mod (suc n)) , mod< _ ((fst x) + (fst y))

+/-assoc : {n : ℕ} (x y z : Fin (suc n)) → (x +/ y) +/ z ≡ (x +/ (y +/ z))
+/-assoc {n = n} x y z =
  Σ≡Prop (λ _ → m<n-isProp)
       ((modR (suc n) ((fst x + fst y) mod (suc n)) (fst z))
    ∙∙ sym (mod-mod (suc n) (fst x + fst y) (fst z))
    ∙∙ cong (_mod suc n) (sym (+-assoc (fst x) (fst y) (fst z)))
    ∙∙ mod-mod (suc n) (fst x) (fst y + fst z)
    ∙∙ sym (modL (suc n) (fst x) ((fst y + fst z) mod suc n)))

+/-comm : {n : ℕ} (x y : Fin (suc n)) → (x +/ y) ≡ (y +/ x)
+/-comm {n = n} x y = Σ≡Prop (λ _ → m<n-isProp) (cong (_mod suc n) (+-comm (fst x) (fst y)))

0+_ : {n : ℕ} (x : Fin (suc n)) → fzero +/ x ≡ x
0+_ {n = n} (x , p) = Σ≡Prop (λ _ → m<n-isProp) (+inductionBase n _ _ _ x p)

_+0 : {n : ℕ} (x : Fin (suc n)) → x +/ fzero ≡ x
_+0 x = +/-comm x fzero ∙ (0+ x)

private
  -help : (n : ℕ) → ℕ → ℕ
  -help n = +induction n _ (λ x _ → ((suc n) ∸ x) mod (suc n)) λ _ x → x

  ≡<-trans : {x y z : ℕ} → x < y → x ≡ z → z < y
  ≡<-trans (k , p) q = k , cong (λ x → k + suc x) (sym q) ∙ p

  -x< : {n : ℕ} → (x : ℕ) → -help n x < suc n
  -x< {n = n} =
    +induction n _ (λ x p → ≡<-trans (mod< n (suc n ∸ x))
                                      (sym (+inductionBase n _ (λ x _ → ((suc n) ∸ x) mod (suc n)) (λ _ x → x) x p)))
                   λ x p → ≡<-trans p (sym (+inductionStep n _ (λ x _ → ((suc n) ∸ x) mod (suc n)) (λ _ x → x) x))

-/_ : {n : ℕ} → (x : Fin (suc n)) → Fin (suc n)
-/_ {n = n} x  = -help n (fst x) , -x< (fst x)

_-/_ : {n : ℕ} → (x y : Fin (suc n)) → Fin (suc n)
_-/_ x y = x +/ (-/ y)

+/-rCancel : {n : ℕ} (x : Fin (suc n)) → x -/ x ≡ 0
+/-rCancel {n = n} x =
  Σ≡Prop (λ _ → m<n-isProp)
      (cong (λ z → (fst x + z) mod (suc n)) (+inductionBase n _ (λ x _ → ((suc n) ∸ x) mod (suc n)) (λ _ x → x) (fst x) (snd x)) 
    ∙∙ sym (modR (suc n) (fst x) ((suc n) ∸ (fst x)))
    ∙∙ cong (_mod (suc n)) (+-comm (fst x) ((suc n) ∸ (fst x)))
    ∙∙ cong (_mod (suc n)) (≤-∸-+-cancel (<-weaken (snd x)))
    ∙∙ zero-charac (suc n))

+/-lCancel : {n : ℕ} (x : Fin (suc n)) → (-/ x) +/ x ≡ 0
+/-lCancel {n = n} x = +/-comm (-/ x) x ∙ +/-rCancel x




open import Cubical.HITs.S1 hiding (_·_ ; encode ; decode)
open import Cubical.Data.Int using (pos ; Int)
open import Cubical.HITs.Truncation renaming (rec to trRec ; elim to trElim)

-- decode proof
data B-Z/ (n : ℕ) : Type₀ where
  [_] : S¹ → B-Z/ n
  kill : cong [_] (intLoop (pos n)) ≡ refl


ℤ/_ : (n : ℕ) → Type
ℤ/ zero = Int
ℤ/ suc n = Fin (suc n)

B-Z/-elim : ∀ {ℓ} (n : ℕ) {A : B-Z/ n → Type ℓ}
                  (f : (x : S¹) → A [ x ])
               → PathP (λ i → PathP (λ j → A (kill i j)) (f base) (f base)) (cong f (intLoop (pos n))) (λ _ → f base)
               → (x : _) → A x
B-Z/-elim n f p [ x ] = f x
B-Z/-elim n f p (kill i i₁) = p i i₁

B-Z/-toPropelim : ∀ {ℓ} (n : ℕ) {A : B-Z/ n → Type ℓ}
               → ((x : _) → isProp (A x))
               → (x₀ : A [ base ])
               → (x : _) → A x
B-Z/-toPropelim n prop f =
  B-Z/-elim _
    (toPropElim (λ _ → prop _) f)
    (isProp→PathP (λ i → isOfHLevelPathP 1 (prop _) _ _) _ _)

B-Z/-toSetelim : ∀ {ℓ} (n : ℕ) {A : B-Z/ n → Type ℓ}
               → ((x : _) → isSet (A x))
               → (f : (x : S¹) → A [ x ])
               → (x : _) → A x
B-Z/-toSetelim n set f =
  B-Z/-elim _ f (toPathP (isOfHLevelPathP' 1 (set _) _ _ _ _))

1f : {n : ℕ} → Fin (suc n)
1f {n = zero} = 0 , 0 , refl
1f {n = suc n} = 1 , n , +-comm n 2

1f≤1 : (n : ℕ) → fst (1f {n = n}) ≤ 1
1f≤1 zero = 1 , refl
1f≤1 (suc n) = 0 , refl

+1Iso : (n : ℕ) → Iso (Fin (suc n)) (Fin (suc n))
Iso.fun (+1Iso n) = 1f +/_
Iso.inv (+1Iso n) = (-/ 1f) +/_
Iso.rightInv (+1Iso n) x = sym (+/-assoc 1f (-/ 1f) x) ∙∙ cong (_+/ x) (+/-rCancel 1f) ∙∙ (0+ x)
Iso.leftInv (+1Iso n) x = sym (+/-assoc (-/ 1f) 1f x) ∙∙ cong (_+/ x) (+/-lCancel 1f) ∙∙ (0+ x)

-/1f : (n : ℕ) → (fst (-/ (1f {n = n})) ≡ n)
-/1f zero = refl
-/1f (suc n) = +inductionBase (suc n) _ (λ x _ → ((2 + n) ∸ x) mod (2 + n)) (λ _ x → x) (fst (1f {n = (suc n)})) (snd 1f)
             ∙ +inductionBase (suc n) (λ _ → ℕ) (λ x _ → x) (λ _ x → x) (suc n) (0 , refl)

cod'S1 : (n : ℕ) → S¹ → Type₀
cod'S1 n base = Fin (suc n)
cod'S1 n (loop i) = isoToPath (+1Iso n) i

comp^ : ∀ {ℓ} {A : Type ℓ} → (n : ℕ) → (A → A) → A → A
comp^ zero f x = x
comp^ (suc n) f = comp^ n f ∘ f

∙^ : ∀ {ℓ} {A : Type ℓ} {x : A} → ℕ → x ≡ x → x ≡ x
∙^ zero p = refl
∙^ (suc n) p = ∙^ n p ∙ p

compIsEquiv^ : ∀ {ℓ} {A : Type ℓ} → (n : ℕ) → (f : A → A) → isEquiv f → isEquiv (comp^ n f)
compIsEquiv^ zero f e = idEquiv _ .snd
compIsEquiv^ (suc n) f e = compEquiv (f , e) (comp^ n f , compIsEquiv^ n f e) .snd

compEquiv^ : ∀ {ℓ} {A : Type ℓ} → (n : ℕ) → A ≃ A → A ≃ A
compEquiv^ zero e = idEquiv _
compEquiv^ (suc n) e = compEquiv e (compEquiv^ n e)


intLoopʳ : (n : ℕ) → intLoop (pos (suc n)) ≡ loop ∙ intLoop (pos n)
intLoopʳ zero = sym (lUnit loop) ∙ rUnit loop
intLoopʳ (suc n) = cong (_∙ loop) (intLoopʳ n) ∙ sym (assoc loop (intLoop (pos n)) loop)

toCompEquiv₁ : (m n : ℕ) → cong (cod'S1 m) (intLoop (pos (suc n))) ≡ ua (compEquiv^ (suc n) (isoToEquiv (+1Iso m)))
toCompEquiv₁ m zero = cong (cong (cod'S1 m)) (sym (lUnit loop)) ∙ cong ua (Σ≡Prop (λ _ → isPropIsEquiv _) refl)
toCompEquiv₁ m (suc n) =
     cong (cong (cod'S1 m)) (intLoopʳ (suc n)) ∙
     congFunct (cod'S1 m) loop (intLoop (pos (suc n)))
  ∙∙ cong (cong (cod'S1 m) loop ∙_) (toCompEquiv₁ m n)
  ∙∙ sym (uaCompEquiv (isoToEquiv (+1Iso m)) (compEquiv^ (suc n) (isoToEquiv (+1Iso m))))
   ∙ cong ua (Σ≡Prop (λ _ → isPropIsEquiv _) refl)

toCompEquiv₃ : (m n : ℕ) (x : _) → (p : suc m < suc n) → compEquiv^ (suc m) (isoToEquiv (+1Iso n)) .fst x ≡ ((fst x + suc m) mod (suc n) , (mod< n (fst x + suc m)))
toCompEquiv₃ m zero x p = isContr→isProp isContrFin1 _ _
toCompEquiv₃ zero (suc n) x (k , p) = 
  Σ≡Prop (λ _ → m≤n-isProp)
         (cong (_mod (2 + n)) (+-comm 1 (fst x)))
toCompEquiv₃ (suc m) (suc n) x (k , p) = 
  Σ≡Prop (λ _ → m≤n-isProp)
         ((λ i → fst (toCompEquiv₃ m (suc n) (1f +/ x) (suc k , sym (+-suc k (2 + m)) ∙ p) i))
       ∙∙ sym (modL (2 + n) (1 + (fst x)) (suc m))
       ∙∙ cong (_mod (2 + n)) (cong (_+ suc m) (+-comm 1 (fst x)) ∙ sym (+-assoc (fst x) 1 (suc m))))

1f+n : {n : ℕ} → 1f {n = n} +/ (n , 0 , refl) ≡ fzero
1f+n {n = zero} = refl
1f+n {n = suc n} =
  Σ≡Prop (λ _ → m≤n-isProp)
         (cong (_mod (suc (suc n))) (λ i → 2 + (+-comm 0 n i))
      ∙∙ +inductionStep (suc n) (λ _ → ℕ) (λ x _ → x) (λ _ x → x) 0
      ∙∙ +inductionBase (suc n) (λ _ → ℕ) (λ x _ → x) (λ _ x → x) 0 (suc n , +-comm (suc n) 1))


toCompEquiv₂ : (n : ℕ) → compEquiv^ (suc (suc n)) (isoToEquiv (+1Iso (suc n))) .fst ≡ λ x → x
toCompEquiv₂ n = funExt λ x →((λ i → (compEquiv^ (suc n) (isoToEquiv (+1Iso (suc n))) .fst (1f +/ x)) )
              ∙∙ toCompEquiv₃ n (suc n) (1f +/ x) (0 , refl)
              ∙∙ Σ≡Prop (λ _ → m≤n-isProp)
                        ((cong fst (cong (_+/ (suc n , 0 , refl)) (+/-comm 1f x)
                                ∙∙ +/-assoc x 1f (suc n , 0 , refl)
                                ∙∙ cong (x +/_) 1f+n
                                 ∙ (x +0)))))



later : (n : ℕ) → cong (cod'S1 n) (intLoop (pos n) ∙ loop) ≡ (λ _ → Fin (suc n))
later zero = cong (cong (cod'S1 zero)) (sym (lUnit loop))  ∙∙ (cong ua help) ∙∙ uaIdEquiv
  where
  help : isoToEquiv (+1Iso zero) ≡ idEquiv _
  help = Σ≡Prop (λ _ → isPropIsEquiv _)
                (funExt λ x → isOfHLevelSuc 0 isContrFin1 _ _)
later (suc n) = toCompEquiv₁ (suc n) (suc n) ∙∙ cong ua (Σ≡Prop (λ _ → isPropIsEquiv _) (toCompEquiv₂ n)) ∙∙ uaIdEquiv


cod' : (n : ℕ) → (x : B-Z/ (suc n)) → Type₀
cod' n = B-Z/-elim (suc n) (cod'S1 n) (later n)

dec'' : (n : ℕ) → (x : B-Z/ (suc n))→ cod' n x → hLevelTrunc 2 ([ base ] ≡ x)
dec'' n = B-Z/-toSetelim (suc n) (λ _ → isSetΠ (λ _ → isOfHLevelTrunc 2))
            help
  where
  pathp : (n : ℕ) → PathP (λ i → cod' n [ loop i ] → Path (B-Z/ (suc n)) [ base ] [ loop i ])
                            (λ p → (λ i → [ intLoop (pos (fst p)) i ]))
                            λ p → (λ i → [ intLoop (pos (fst p)) i ])
  pathp n =
    toPathP (funExt λ p → (λ k → transport (λ i → Path (B-Z/ (suc n)) [ base ] [ loop i ]) λ i → [ intLoop (pos (fst ((-/ 1f) +/ transportRefl p k))) i ])
                        ∙∙ (λ k → transp (λ i → Path (B-Z/ (suc n)) [ base ] [ loop (i ∨ k) ]) k λ i → [ compPath-filler (intLoop (pos (fst ((-/ 1f) +/ p)))) (loop) k i ])
                        ∙∙ help p)

    where
    help : (p : Fin (suc n)) → (λ i → [ (intLoop (pos (suc (fst ((-/ 1f) +/ p))))) i ]) ≡  (λ i → [ intLoop (pos (fst p)) i ])
    help (zero , _) = (λ k i → [ (intLoop (pos (suc (fst ((_+0 {n = n} (-/ 1f)) k))))) i ])
                    ∙∙ (λ k i → [ intLoop (pos (suc (-/1f n k) )) i ])
                    ∙∙ kill
    help (suc p , s) = ((λ k i → [ (intLoop (pos (suc (fst ((-/ 1f) +/ help2 n p s K k))))) i ]))
                    ∙∙ (λ k i → [ (intLoop (pos (suc (fst (+/-assoc (-/ 1f) 1f (p , K) (~ k)))))) i ])
                    ∙∙ ((λ k i → [ (intLoop (pos (suc (fst ((+/-lCancel 1f k) +/ (p , K)))))) i ]))
                     ∙ (λ k i → [ (intLoop (pos (suc (fst ((0+ (p , K)) k))))) i ])
      where
      K = (suc (fst s) , sym (+-suc (fst s) (suc p)) ∙ snd s)

      help2 : (n : ℕ) → (x : ℕ) (k : _) (s : _) → Path (Fin (suc n)) (suc x , k) (1f +/ (x , s))
      help2 zero x (zero , p) s = ⊥-rec (snotz (cong predℕ p))
      help2 zero x (suc zero , p) s = ⊥-rec (snotz (cong predℕ p))
      help2 zero x (suc (suc k) , p) s = ⊥-rec (snotz (cong predℕ p))
      help2 (suc n) x k s =  Σ≡Prop (λ _ → m≤n-isProp) (sym (+inductionBase (suc n) (λ _ → ℕ) (λ x₁ _ → x₁) (λ _ x₁ → x₁) (suc x) k))


 
  help : (x : S¹) → cod' n [ x ] → hLevelTrunc 2 ([ base ] ≡ [ x ])
  help base p = ∣ (λ i → [ intLoop (pos (fst p)) i ]) ∣
  help (loop i) p =  ∣ pathp n i p ∣

isSet-cod : (n : ℕ) (x : _) → isSet (cod' n x)
isSet-cod n = B-Z/-toPropelim _ (λ _ → isPropIsSet) isSetFin

-- B-Z/-toPropelim

¬suc<1 : {x : ℕ} → ¬ (suc x < 1)
¬suc<1 {x = zero} (zero , k) = snotz (cong predℕ k)
¬suc<1 {x = zero} (suc zero , k) = snotz (cong predℕ k)
¬suc<1 {x = zero} (suc (suc p) , k) = snotz (cong predℕ k)
¬suc<1 {x = suc x} (zero , k) = snotz (cong predℕ k)
¬suc<1 {x = suc x} (suc zero , k) = snotz (cong predℕ k)
¬suc<1 {x = suc x} (suc (suc p) , k) = snotz (cong predℕ k)

enc'' : (n : ℕ) → (x : B-Z/ (suc n))→  hLevelTrunc 2 ([ base ] ≡ x) → cod' n x
enc'' n x = trRec (isSet-cod n x) λ p → subst (cod' n) p fzero

enc-dec-lem : (n : ℕ) (p : ℕ) (sn : p < suc n) → (subst (cod' n) (λ i → [ intLoop (pos p) i ]) fzero) ≡ (p , sn)
enc-dec-lem n zero q = Σ≡Prop (λ _ → m≤n-isProp) refl
enc-dec-lem zero (suc p) q = ⊥-rec (¬suc<1 q)
enc-dec-lem (suc n) (suc p) q =
   Σ≡Prop (λ _ → m≤n-isProp) ((λ k → fst (transport (λ i → cod' (suc n) (congFunct (λ x → [ x ])  (intLoop (pos p)) loop k i)) fzero))
                          ∙∙ cong fst (substComposite (cod' (suc n)) (λ i → [ intLoop (pos p) i ]) (λ i → [ loop i ]) fzero)
                          ∙∙ cong fst (cong (subst (cod' (suc n)) (λ i → [ loop i ]))
                                            (enc-dec-lem (suc n) p (suc (fst q) , sym (+-suc (fst q) (suc p)) ∙ (snd q))))
                          ∙∙ transportRefl ((fst (1f {n = (suc n)}) + p) mod suc (suc n))
                          ∙∙ +inductionBase (suc n) (λ _ → ℕ) (λ x _ → x) (λ _ x → x) (suc p) q)

enc-dec : (n : ℕ) →  (p : cod' n [ base ]) → enc'' n [ base ] (dec'' n _ p) ≡ p
enc-dec n p = Σ≡Prop (λ _ → m≤n-isProp) (cong fst (enc-dec-lem n (fst p) (snd p)))

dec-enc : (n : ℕ) → (x : B-Z/ (suc n)) → (p : hLevelTrunc 2 ([ base ] ≡ x)) → dec'' n x (enc'' n x p) ≡ p
dec-enc n x =
  trElim (λ _ → isOfHLevelPath 2 (isOfHLevelTrunc 2) _ _)
         (J (λ x p → dec'' n x (enc'' n x ∣ p ∣) ≡ ∣ p ∣) refl)


test : (n : ℕ) → Iso (hLevelTrunc 2 (Path (B-Z/ (suc n)) [ base ] [ base ])) (Fin (suc n))
Iso.fun (test n) = enc'' n [ base ]
Iso.inv (test n) = dec'' n [ base ]
Iso.rightInv (test n) = enc-dec n
Iso.leftInv (test n) = dec-enc n [ base ]

deLoopingFiniteSet : (n : ℕ) → Iso (Path (hLevelTrunc 3 (B-Z/ (suc n))) ∣ [ base ] ∣ ∣ [ base ] ∣) (Fin (suc n))
deLoopingFiniteSet n = compIso (PathIdTruncIso 2) (test n)

mappie : (n : ℕ) → Path (hLevelTrunc 3 (B-Z/ (suc n))) ∣ [ base ] ∣ ∣ [ base ] ∣ → ℕ
mappie n p = fst (Iso.fun (deLoopingFiniteSet n) p)

{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.HITs.Delooping.n.base where

open import Cubical.HITs.Susp
-- open import Cubical.Data.Int
open import Cubical.HITs.Pushout
open import Cubical.Data.Nat -- hiding (elim) renaming (_+_ to _+N_ ; +-comm to +N-comm ; ·-comm to ·ℕ-comm ; +-assoc to +ℕ-assoc ; _·_ to _·N_)
open import Cubical.Data.Fin
open import Cubical.Data.Nat.Order
-- open import Cubical.Foundation.Prelims
open import Cubical.Foundations.Everything


open import Cubical.HITs.SetQuotients
open import Cubical.Relation.Nullary
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group
open import Cubical.Algebra.Semigroup

open IsMonoid
open CommRingStr renaming (_+_ to _+r_ ; _·_ to _·r_ ; -_ to -r_)
open IsCommRing
open IsRing
open IsAbGroup
open IsSemigroup
open IsGroup

open import Cubical.Data.Empty

open import Cubical.Data.Nat.GCD
open import Cubical.Data.Sigma
open import Cubical.Data.Sum

open import Cubical.Data.Empty renaming (rec to ⊥-rec)

Z/ : (n : ℕ) → Type₀
Z/ n = Fin n

0/ : {n : ℕ} → Fin (suc n)
0/ {n = n} = 0 , (n , (+-comm n 1))

1/ : {n : ℕ} → Fin (suc n)
1/ {n = zero} = 0/
1/ {n = suc n} = 1 , (n , +-comm n 2)


∸∸ : (x : ℕ) → x ∸ x ≡ 0
∸∸ zero = refl
∸∸ (suc x) = ∸∸ x

suc-∸ : (x y : ℕ) → (y ≤ x) → suc (x ∸ y) ≡ suc x ∸ y
suc-∸ x zero _ = refl
suc-∸ zero (suc y) (zero , p) = ⊥-rec (snotz p)
suc-∸ zero (suc y) (suc k , p) = ⊥-rec (snotz p)
suc-∸ (suc x) (suc y) p = suc-∸ x y (pred-≤-pred p)

rCancel∸ : (x y : ℕ) → (x + y) ∸ y ≡ x
rCancel∸ x zero = +-comm x zero
rCancel∸ zero x = ∸∸ x
rCancel∸ (suc x) (suc y) = cong (_∸ y) (+-suc x y) ∙ rCancel∸ (suc x) y

assocˡ∸ : (x y z : ℕ) → z ≤ y → x + (y ∸ z) ≡ (x + y) ∸ z
assocˡ∸ x y zero (k , p) = refl
assocˡ∸ x zero (suc z) (zero , p) = ⊥-rec (snotz p)
assocˡ∸ x zero (suc z) (suc k , p) = ⊥-rec (snotz p)
assocˡ∸ zero (suc y) (suc z) (k , p) = refl
assocˡ∸ (suc x) (suc y) (suc z) (k , p) = assocˡ∸ (suc x) y z (pred-≤-pred (_ , p))
                                        ∙ cong (_∸ z) (sym (+-suc x y))

cong∸< : (x y z : ℕ) → z ≤ x → x < y → (x ∸ z) < y ∸ z
cong∸< x y z (k , <z) (r , <y) = r , helper x y r k z <y <z
  where
  helper2 : (x y z r : ℕ) → r + suc x ≡ y → z ≤ x → r + (suc x ∸ z) ≡ y ∸ z
  helper2 x y z r q p = assocˡ∸ r (suc x) z ((suc (fst p)) , cong suc (snd p))
                      ∙ cong (_∸ z) q

  helper : (x y r k z : ℕ) → r + suc x ≡ y → k + z ≡ x → r + suc (x ∸ z) ≡ y ∸ z
  helper x y r k z p q = cong (r +_) (suc-∸ x z ((k , q))) ∙ helper2 x y z r p (k , q)


<≡-trans : {x y z : ℕ} → x < y → y ≡ z → x < z
<≡-trans (k , p) q = k , p ∙ q

≡<-trans : {x y z : ℕ} → x < y → x ≡ z → z < y
≡<-trans (k , p) q = k , cong (k +_) (cong suc (sym q)) ∙ p

≤≡-trans : {x y z : ℕ} → x ≤ y → y ≡ z → x ≤ z
≤≡-trans (k , p) q = k , p ∙ q

≡≤-trans : {x y z : ℕ} → x ≤ y → x ≡ z → z ≤ y
≡≤-trans (k , p) q = k , cong (k +_) (sym q) ∙ p

≤-+k-uncancel : {m k n : ℕ} → m ≤ n → m + k ≤ n + k
≤-+k-uncancel {m} {k} {n} (r , p) = r , +-assoc r m k ∙ cong (_+ k) p

<-+k-uncancel : {m k n : ℕ} → m < n → m + k < n + k
<-+k-uncancel {m} {k} {n} (r , p) = r , +-assoc r (suc m) k ∙ cong (_+ k) p

+-<-trans : (x xmax y ymax : ℕ) → x < xmax → y < ymax → x + y < xmax + ymax
fst (+-<-trans x xmax y ymax (xk , xp) (yk , yp)) = suc xk + yk
snd (+-<-trans x xmax y ymax (xk , xp) (yk , yp)) =
     sym (+-suc (xk + yk) (suc (x + y)))
  ∙∙ cong ((xk + yk) +_) (sym (+-suc (suc x) y))
  ∙∙ (λ i → +-assoc xk yk (+-comm (suc x) (suc y) i) (~ i))
  ∙∙ cong (xk +_) (+-assoc yk (suc y) (suc x))
  ∙∙ cong (xk +_) (+-comm (yk + suc y) (suc x))
  ∙∙ +-assoc xk (suc x) (yk + suc y)
  ∙∙ cong₂ _+_ xp yp


+-≤-trans : (x xmax y ymax : ℕ) → x ≤ xmax → y ≤ ymax → x + y ≤ xmax + ymax
fst (+-≤-trans x xmax y ymax (xk , xp) (yk , yp)) = yk + xk
snd (+-≤-trans x xmax y ymax (xk , xp) (yk , yp)) =
     +-comm (yk + xk) (x + y)
  ∙∙ sym (+-assoc x y (yk + xk))
  ∙∙ cong (x +_) (+-assoc y yk xk)
  ∙∙ cong (x +_) (+-comm (y + yk) xk) -- +-assoc x (y + yk) xk
  ∙∙ +-assoc x xk (y + yk)
  ∙∙ cong₂ _+_ (+-comm x xk) (+-comm y yk)
  ∙∙ cong₂ _+_ xp yp

incl : (n x : ℕ) → (x < (suc n)) ⊎ ((suc n ≤ x) × (x < (2 · (suc n)))) → Fin (suc n)
fst (incl n x (inl p)) = x
snd (incl n x (inl p)) = p
fst (incl n x (inr ((l , p) , p2))) = x ∸ (suc n)
fst (snd (incl n x (inr ((l , p) , p2)))) = fst (cong∸< x (2 · (suc n)) (suc n) (l , p) p2)
snd (snd (incl n x (inr ((l , p) , p2)))) =
     snd (cong∸< x (2 · (suc n)) (suc n) (l , p) p2)
  ∙∙ cong (λ x → (n + suc x) ∸ n) (+-comm n zero)
  ∙∙ cong (_∸ n) (+-suc n n)
   ∙ rCancel∸ (suc n) n

pm-typ : {n : ℕ} → (x y : Fin (suc n)) → Type₀
pm-typ {n = n} x y = (fst x + fst y < (suc n)) ⊎ ((suc n) ≤ fst x + fst y)

pm-typ-help : {n : ℕ} → (x : ℕ) → (x < (suc n)) ⊎ ((suc n) ≤ x)
pm-typ-help {n = n} zero = inl (n , +-comm n 1)
pm-typ-help {n = n} (suc x) with pm-typ-help x
... | inl (zero , p) = inr (0 , sym p)
... | inl (suc k , p) = inl (k , +-suc k (suc x) ∙ p)
... | inr (k , p) = inr (suc k , cong suc p)

+/-help : {n : ℕ} → (x y : Fin (suc n)) → pm-typ x y → Fin (suc n)
+/-help {n = n} x y (inl z) = incl n (fst x + fst y) (inl z)
+/-help {n = n} x y (inr z) = incl n (fst x + fst y) (inr (z , <≡-trans (+-<-trans (fst x) (suc n) (fst y) (suc n) (snd x) (snd y)) (cong suc (cong (n +_) (cong suc (+-comm zero n))))))

∸→≤ : (x y : ℕ) → x ∸ y ≤ x
∸→≤ x zero = 0 , refl
∸→≤ zero (suc y) = 0 , refl
∸→≤ (suc x) (suc y) = ≤-trans (∸→≤ x y) (1 , refl)

-/_ : {n : ℕ} (x : Fin (suc n)) → Fin (suc n)
-/_ {n = n} (zero , p) = 0 , n , +-comm n 1
-/_ {n = n} (suc x , p) = (n ∸ x) , help n x
  where
  help : (n x : ℕ) → n ∸ x < suc n
  help n zero = 0 , refl
  help zero (suc x) = 0 , refl
  help (suc n) (suc x) = <-trans (help n x) (0 , refl)

0<suc : {n : ℕ} → zero < suc n
0<suc {n = n} = n , +-comm n 1

pred-<-pred : (x y : ℕ) → suc x < suc y → x < y
pred-<-pred x y p = (fst p) , cong predℕ (sym (+-suc (fst p) (suc x)) ∙ snd p)

¬≥&< : (x y : ℕ) → ¬ (y ≤ x) × (x < y)
¬≥&< zero zero ((ley , py) , zero , px) = ⊥-rec (snotz px)
¬≥&< zero zero ((ley , py) , suc lex , px) = ⊥-rec (snotz px)
¬≥&< zero (suc y) ((ley , py) , lex , px) = ⊥-rec (snotz (sym (+-suc ley y) ∙ py))
¬≥&< (suc x) zero ((ley , py) , zero , px) = ⊥-rec (snotz px)
¬≥&< (suc x) zero ((ley , py) , suc lex , px) = ⊥-rec (snotz px)
¬≥&< (suc x) (suc y) (p , r) = ¬≥&< x y (pred-≤-pred p  , pred-<-pred x y r)

rUnit-helper : {n : ℕ} → (x : Fin (suc n)) (p : pm-typ x 0) → fst (+/-help x fzero p) ≡ fst x 
rUnit-helper {n = n} x (inl x₁) = +-comm (fst x) 0
rUnit-helper {n = n} x (inr p) = ⊥-rec (¬≥&< _ _ (≤≡-trans p (+-comm (fst x) 0) , (snd x)))

lUnit-helper : {n : ℕ} → (x : Fin (suc n)) (p : pm-typ 0 x) → fst (+/-help fzero x p) ≡ fst x 
lUnit-helper {n = n} x (inl x₁) = refl
lUnit-helper {n = n} x (inr x₁) = ⊥-rec (¬≥&< _ _ (x₁ , (snd x)))

+/-comm-helper : {n : ℕ} → (x y : Fin (suc n)) (p : pm-typ x y) → Σ[ q ∈ pm-typ y x ] (+/-help x y p ≡ +/-help y x q)
fst (+/-comm-helper {n = n} x y (inl x₁)) = inl ((fst x₁) , cong (λ x → fst x₁ + suc x) (+-comm (fst y) (fst x)) ∙ snd x₁)
snd (+/-comm-helper {n = n} x y (inl x₁)) = Σ≡Prop (λ x → m<n-isProp) (+-comm (fst x) (fst y))
fst (+/-comm-helper {n = n} x y (inr p)) = inr (≤≡-trans p (+-comm (fst x) (fst y)))
snd (+/-comm-helper {n = n} x y (inr p)) = Σ≡Prop (λ x → m<n-isProp) (cong (_∸ (suc n)) (+-comm (fst x) (fst y)))

pm-typ0r : {n : ℕ} (x : Fin (suc n)) → pm-typ x 0
pm-typ0r (x , (k , p)) = inl (k , cong (λ x → k + suc x) (+-comm x 0) ∙ p)

isPropPm-typ : {n : ℕ} (x y : Fin (suc n)) → isProp (pm-typ x y)
isPropPm-typ x y (inl p) (inl q) i = inl (m<n-isProp p q i)
isPropPm-typ x y (inl p) (inr q) = ⊥-rec (¬≥&< _ _ (q , p))
isPropPm-typ x y (inr p) (inl q) = ⊥-rec (¬≥&< _ _ (q , (fst p) , (+-suc (fst p) (suc _) ∙ cong suc (snd p))))
isPropPm-typ x y (inr p) (inr q) i = inr (m≤n-isProp p q i)

rCancel-helper : {n : ℕ} (x : Fin (suc n)) (p : pm-typ x (-/ x)) → +/-help x (-/ x) p ≡ fzero
rCancel-helper (zero , l , q) (inl p) = Σ≡Prop (λ _ → m<n-isProp) refl
rCancel-helper {n = n} (suc x , l , q) (inl p) = ⊥-rec (¬≥&< _ _ ((0 , cong suc (sym (help l q))) , p))
  where
  help : (l : ℕ) → (l + suc (suc x) ≡ suc n) → x + (n ∸ x) ≡ n
  help zero q = +-comm x (n ∸ x) ∙ ≤-∸-+-cancel (pred-≤-pred (1 , q))
  help (suc l) q = +-comm x (n ∸ x) ∙ ≤-∸-+-cancel (pred-≤-pred (2 + l , cong suc (sym (+-suc l (suc x))) ∙ q))
rCancel-helper (zero , l , q) (inr p) = Σ≡Prop (λ _ → m<n-isProp) refl
rCancel-helper {n = n} (suc x , q) (inr p) =
  Σ≡Prop (λ _ → m<n-isProp)
         (cong (_∸ n) (+-comm x (n ∸ x))
      ∙∙ cong (_∸ n) (≤-∸-+-cancel {m = x} {n = n} (pred-≤-pred (<-weaken q)))
      ∙∙ ∸∸ n)

lCancel-helper : {n : ℕ} (x : Fin (suc n)) (p : pm-typ (-/ x) x) → +/-help (-/ x) x p ≡ fzero
lCancel-helper x p = c .snd ∙ rCancel-helper x (fst c)
  where
  c = +/-comm-helper (-/ x) x p

<-weakenˡ : (x y z : ℕ) → x + y < z → x < z
<-weakenˡ x y z p = fst p + y , sym (+-assoc (fst p) y (suc x)) ∙∙ cong (fst p +_) (+-suc y x ∙ cong suc (+-comm y x)) ∙∙ snd p

+-assoc-helper : {n : ℕ} (x y z : Fin (suc n)) (p : pm-typ x y) (q : pm-typ (+/-help x y p) z)
               → (p2 : pm-typ y z) (q2 : pm-typ x (+/-help y z p2))
               → +/-help x (+/-help y z p2) q2
               ≡ +/-help (+/-help x y p) z q
+-assoc-helper x y z (inl p) (inl q) (inl p2) (inl q2) =
  Σ≡Prop (λ _ → m<n-isProp) (+-assoc (fst x) (fst y) (fst z))
+-assoc-helper x y z (inl p) (inl q) (inl p2) (inr q2) =
  ⊥-rec (¬≥&< _ _ (q2 , ≡<-trans q (sym (+-assoc (fst x) (fst y) (fst z)))))
+-assoc-helper {n = n} x y z (inl p) (inl q) (inr p2) (inl q2) =
  ⊥-rec (¬≥&< _ _ (p2 , <-weakenˡ (fst y + fst z) (fst x) (suc n)
                           (≡<-trans q (sym (+-assoc (fst x) (fst y) (fst z))
                                      ∙ sym (+-comm (fst y + fst z) (fst x))))))
+-assoc-helper {n = n} x y z (inl p) (inl q) (inr p2) (inr q2) =
  ⊥-rec (¬≥&< _ _ (p2 , <-weakenˡ (fst y + fst z) (fst x) (suc n)
                           (≡<-trans q (sym (+-assoc (fst x) (fst y) (fst z))
                                       ∙ sym (+-comm (fst y + fst z) (fst x))))))
+-assoc-helper x y z (inl p) (inr q) (inl p2) (inl q2) =
  ⊥-rec (¬≥&< _ _ (q , ≡<-trans q2 (+-assoc (fst x) (fst y) (fst z))))
+-assoc-helper {n = n} x y z (inl p) (inr q) (inl p2) (inr q2) =
  Σ≡Prop (λ _ → m<n-isProp) (cong (_∸ suc n) (+-assoc (fst x) (fst y) (fst z)))
+-assoc-helper {n = n} x y z (inl p) (inr q) (inr p2) (inl q2) =
  Σ≡Prop (λ _ → m<n-isProp) (assocˡ∸ (fst x) _ _ p2 ∙ cong (_∸ suc n) (+-assoc (fst x) (fst y) (fst z)))
+-assoc-helper {n = n} x y z (inl p) (inr q) (inr p2) (inr q2) = ⊥-rec (¬≥&< _ _ (l , r))
  where
  r : (fst x) + (fst y) + (fst z) < 2 · suc n
  r = <≡-trans (+-<-trans (fst x + fst y) (suc n) (fst z) (suc n) p (snd z))
               (cong suc (cong (n +_) (cong suc (+-comm 0 n))))

  l : 2 · suc n ≤ (fst x) + (fst y) + (fst z)
  l = ≡≤-trans (≤≡-trans (≤-+k-uncancel {k = suc n} (≤≡-trans q2 (assocˡ∸ (fst x) (fst y + fst z) _ p2)))
                   (+-comm ((fst x + (fst y + fst z)) ∸ suc n) (suc n)
                 ∙∙ assocˡ∸ (suc n) (fst x + (fst y + fst z)) (suc n) (≤≡-trans q (sym (+-assoc (fst x) (fst y) (fst z))))
                  ∙ (λ i → (+-comm n (+-assoc (fst x) (fst y) (fst z) i) i) ∸ n)
                 ∙∙ rCancel∸ (fst x + fst y + fst z) n))
               (cong suc (cong (n +_) (cong suc (+-comm 0 n))))
+-assoc-helper x y z (inr p) (inl q) (inl p2) (inl q2) =
  ⊥-rec (¬≥&< _ _ (p , (<-weakenˡ _ (fst z) _ (≡<-trans q2 (+-assoc (fst x) (fst y) (fst z))))))
+-assoc-helper {n = n} x y z (inr p) (inl q) (inl p2) (inr q2) =
  Σ≡Prop (λ _ → m<n-isProp)
       (cong (_∸ suc n) (+-comm (fst x) (fst y + fst z)
                      ∙∙ sym (+-assoc (fst y) (fst z) (fst x))
                      ∙∙ +-comm (fst y) (fst z + fst x)
                       ∙ sym (+-assoc (fst z) (fst x) (fst y)))
     ∙∙ sym (assocˡ∸ (fst z) (fst x + fst y) (suc n) p)
     ∙∙ +-comm (fst z) ((fst x + fst y) ∸ (suc n)))
+-assoc-helper {n = n} x y z (inr p) (inl q) (inr p2) (inl q2) =
  Σ≡Prop (λ _ → m<n-isProp)
      (assocˡ∸ (fst x) (fst y + fst z) (suc n) p2
    ∙∙ cong (_∸ (suc n)) (+-assoc (fst x) (fst y) (fst z))
    ∙∙ cong (_∸ (suc n)) (+-comm (fst x + fst y) (fst z))
    ∙∙ sym (assocˡ∸ (fst z) (fst x + fst y) (suc n) p)
    ∙∙ +-comm (fst z) (fst x + fst y ∸ suc n))
+-assoc-helper {n = n} x y z (inr p) (inl q) (inr p2) (inr q2) =
  ⊥-rec (¬≥&< _ _ (q2 , (≡<-trans q (+-comm (fst x + fst y ∸ (suc n)) (fst z)
                      ∙∙ assocˡ∸ (fst z) (fst x + fst y) (suc n) p
                      ∙∙ cong (_∸ suc n) (+-comm (fst z) (fst x + fst y))
                      ∙∙ cong (_∸ suc n) (sym (+-assoc (fst x) (fst y) (fst z)))
                      ∙∙ sym (assocˡ∸ (fst x) (fst y + fst z) (suc n) p2)))))
+-assoc-helper x y z (inr p) (inr q) (inl p2) (inl q2) =
  ⊥-rec (¬≥&< _ _ (((fst p) + (fst z)
                  , (sym (+-assoc (fst p) (fst z) (suc _))
                  ∙∙ cong (fst p +_) (+-comm (fst z) (suc _))
                  ∙∙ +-assoc (fst p) (suc _) (fst z)
                  ∙∙ cong (_+ fst z) (snd p)
                  ∙∙ sym (+-assoc (fst x) (fst y) (fst z)))) , q2))
+-assoc-helper {n = n} x y z (inr p) (inr q) (inl p2) (inr q2) =
  ⊥-rec (¬≥&< _ _ (lem , <≡-trans (+-<-trans (fst x) (suc n) (fst y + fst z) (suc n) (snd x) p2)
                                   λ i → suc (n + suc (+-comm n zero (~ i))) ))
  where
  lem1 : fst z + (fst x + fst y) ≡ fst x + (fst y + fst z)
  lem1 = +-comm (fst z) (fst x + fst y) ∙ sym (+-assoc (fst x) (fst y) (fst z))

  lem2 : fst x + (fst y + fst z) ≡ fst z + (fst x + fst y)
  lem2 = cong (fst x +_) (+-comm (fst y) (fst z))
      ∙∙ +-comm (fst x) (fst z + fst y)
      ∙∙ sym (+-assoc (fst z) (fst y) (fst x))
       ∙ cong (fst z +_) (+-comm (fst y) (fst x))

  lem : 2 · suc n ≤ fst x + (fst y + fst z)
  lem = ≤≡-trans (≡≤-trans (≤-+k-uncancel {k = (suc n)} q) (λ i → suc (n + suc (+-comm n zero (~ i)))))
                    (cong (_+ suc n) (+-comm (fst x + fst y ∸ suc n) (fst z))
                 ∙∙ cong (_+ suc n) (assocˡ∸ (fst z) (fst x + fst y) (suc n) p)
                 ∙∙ +-comm (fst z + (fst x + fst y) ∸ suc n) (suc n) 
                 ∙∙ assocˡ∸ (suc n) (fst z + (fst x + fst y)) (suc n) (≤≡-trans q2 lem2)
                 ∙∙ cong (_∸ n) (+-comm n (fst z + (fst x + fst y)))
                 ∙∙ rCancel∸ (fst z + (fst x + fst y)) n
                 ∙∙ lem1)
+-assoc-helper {n = n} x y z (inr p) (inr q) (inr p2) (inl q2) = ⊥-rec (¬≥&< _ _ (lem , lem<))
  where
  lem1 : fst z + (fst x + fst y) ≡ fst x + (fst y + fst z)
  lem1 = +-comm (fst z) (fst x + fst y) ∙ sym (+-assoc (fst x) (fst y) (fst z))

  lem2 : fst x + (fst y + fst z) ≡ fst z + (fst x + fst y)
  lem2 = cong (fst x +_) (+-comm (fst y) (fst z))
      ∙∙ +-comm (fst x) (fst z + fst y)
      ∙∙ sym (+-assoc (fst z) (fst y) (fst x))
       ∙ cong (fst z +_) (+-comm (fst y) (fst x))

  lem3 : suc n ≤ fst z + (fst x + fst y)
  lem3 = (fst z + fst p) , sym (+-assoc (fst z) (fst p) (suc n)) ∙ cong (fst z +_) (snd p)

  lem : 2 · suc n ≤ fst x + (fst y + fst z)
  lem = ≤≡-trans (≡≤-trans (≤-+k-uncancel {k = (suc n)} q) (λ i → suc (n + suc (+-comm n zero (~ i)))))
                    (cong (_+ suc n) (+-comm (fst x + fst y ∸ suc n) (fst z))
                 ∙∙ cong (_+ suc n) (assocˡ∸ (fst z) (fst x + fst y) (suc n) p)
                 ∙∙ +-comm (fst z + (fst x + fst y) ∸ suc n) (suc n) 
                 ∙∙ assocˡ∸ (suc n) (fst z + (fst x + fst y)) (suc n) lem3
                 ∙∙ cong (_∸ n) (+-comm n (fst z + (fst x + fst y)))
                 ∙∙ rCancel∸ (fst z + (fst x + fst y)) n
                 ∙∙ lem1)

  lem< : fst x + (fst y + fst z) < 2 · suc n
  lem< = ≡<-trans (<≡-trans (<-+k-uncancel {k = (suc n)} q2) (λ i → suc (n + suc (+-comm 0 n i))))
         (+-comm (fst x + (fst y + fst z ∸ suc n)) (suc n)
       ∙∙ +-assoc (suc n) (fst x) (fst y + fst z ∸ suc n)
       ∙∙ assocˡ∸ (suc n + fst x) (fst y + fst z) (suc n) p2
       ∙∙ cong (_∸ n) (sym (+-assoc n (fst x) (fst y + fst z)) ∙ +-comm n (fst x + (fst y + fst z))) 
       ∙∙ rCancel∸ (fst x + (fst y + fst z)) n)
+-assoc-helper {n = n} x y z (inr p) (inr q) (inr p2) (inr q2) =
  Σ≡Prop (λ _ → m<n-isProp)
         (cong (_∸ suc n) help)
  where
  help : fst x + (fst y + fst z ∸ suc n) ≡ fst x + fst y ∸ suc n + fst z
  help = assocˡ∸ (fst x) (fst y + fst z) (suc n) p2
      ∙∙ cong (_∸ suc n) (+-assoc (fst x) (fst y) (fst z))
      ∙∙ cong (_∸ suc n) (+-comm (fst x + fst y) (fst z))
      ∙∙ sym (assocˡ∸ (fst z) (fst x + fst y) (suc n) p)
      ∙∙ +-comm (fst z) (fst x + fst y ∸ suc n)

pm-typ-c : {n : ℕ} (x y : Fin (suc n)) → pm-typ x y
pm-typ-c {n = n} x y = pm-typ-help (fst x + fst y)

_+/_ : {n : ℕ} → Fin (suc n) → Fin (suc n) → Fin (suc n)
_+/_ x y = +/-help x y (pm-typ-c x y)

rCancel+/ : {n : ℕ} → (x : Fin (suc n)) → x +/ (-/ x) ≡ fzero
rCancel+/ x = rCancel-helper x (pm-typ-c x (-/ x))

lCancel+/ : {n : ℕ} → (x : Fin (suc n)) → (-/ x) +/ x ≡ fzero
lCancel+/ x = lCancel-helper x (pm-typ-c (-/ x) x)

+/-comm : {n : ℕ} → (x y : Fin (suc n)) → x +/ y ≡ y +/ x
+/-comm x y = c .snd ∙ cong (+/-help y x) (isPropPm-typ y x (fst c) (pm-typ-c y x))
  where
  c = +/-comm-helper x y (pm-typ-c x y)

rUnit+/ : {n : ℕ} → (x : Fin (suc n)) → x +/ fzero ≡ x 
rUnit+/ x = Σ≡Prop (λ _ → m<n-isProp) (rUnit-helper x (pm-typ-c x fzero))

lUnit+/ : {n : ℕ} → (x : Fin (suc n)) → fzero +/ x ≡ x 
lUnit+/ x = Σ≡Prop (λ _ → m<n-isProp) (lUnit-helper x (pm-typ-c fzero x))

+/-assoc : {n : ℕ} → (x y z : Fin (suc n)) → (x +/ (y +/ z)) ≡ ((x +/ y) +/ z)
+/-assoc x y z =
  +-assoc-helper x y z
    (pm-typ-c x y) (pm-typ-c (x +/ y) z)
    (pm-typ-c y z) (pm-typ-c x (y +/ z))

_^_ : ∀ {ℓ} {A : Type ℓ} {a : A} (p : a ≡ a) (n : ℕ) → a ≡ a
p ^ zero = refl
p ^ suc zero = p
p ^ suc (suc n) = (p ^ (suc n)) ∙ p

open import Cubical.HITs.S1
open import Cubical.Data.Int using (pos)
data B-Z/ (n : ℕ) : Type₀ where
  [_] : S¹ → B-Z/ n
  kill : cong [_] (intLoop (pos n)) ≡ refl

elimB-Z/ : ∀ {ℓ} (n : ℕ) → {A : B-Z/ n → Type ℓ}
         → (f : (x : S¹) → A [ x ])
         → PathP (λ i → PathP (λ j → A (kill i j)) (f base) (f base)) (cong f (intLoop (pos n))) (λ _ → f base)
         → (x : B-Z/ n) → A x
elimB-Z/ n f p [ x ] = f x
elimB-Z/ n f p (kill i j) = p i j

recB-Z/ : ∀ {ℓ} (n : ℕ) → {A :  Type ℓ}
         → (f : S¹ → A)
         → (cong f (intLoop (pos n))) ≡ refl
         → B-Z/ n → A
recB-Z/ n f p [ x ] = f x
recB-Z/ n f p (kill i j) = p i j

1f : {n : ℕ} → Fin (suc n)
1f {n = zero} = 0 ,  0 , refl
1f {n = suc n} = 1 , n , +-comm n 2

+1 : {n : ℕ} → Fin (suc n) → Fin (suc n)
+1 x = 1f +/ x

1- : {n : ℕ} → Fin (suc n) → Fin (suc n)
1- x = (-/ 1f) +/ x

+1Iso : {n : ℕ} → Iso (Fin (suc n)) (Fin (suc n))
Iso.fun (+1Iso {n = n}) = +1
Iso.inv (+1Iso {n = n}) = 1-
Iso.rightInv (+1Iso {n = zero}) x = isContr→isProp isContrFin1 _ _
Iso.rightInv (+1Iso {n = suc n}) x = +/-assoc 1f (-/ 1f) x ∙∙ cong (_+/ x) (rCancel+/ 1f) ∙∙ lUnit+/ x
Iso.leftInv (+1Iso {n = zero}) x = isContr→isProp isContrFin1 _ _
Iso.leftInv (+1Iso {n = suc n}) x = +/-assoc (-/ 1f) 1f x ∙∙ cong (_+/ x) (lCancel+/ 1f) ∙∙ lUnit+/ x

S¹-cod : (n : ℕ) → S¹ → Type₀
S¹-cod n base = Fin (suc n)
S¹-cod n (loop i) = isoToPath (+1Iso {n = n}) i

S¹-cod' : (n : ℕ) → S¹ → Type₀
S¹-cod' n = {!!}

lem' : (n m : ℕ) → cong (S¹-cod n) (intLoop (pos m)) ≡ (isoToPath (+1Iso {n = n}) ^ m)
lem' n zero = refl
lem' n (suc zero) = cong (cong (S¹-cod n)) (sym (lUnit loop))
lem' n (suc (suc m)) = congFunct (S¹-cod n) (intLoop (pos (suc m))) loop ∙ cong (_∙ isoToPath (+1Iso {n = n})) (lem' n (suc m))

lem : (n : ℕ) → cong (S¹-cod n) (intLoop (pos n) ∙ loop) ≡ (isoToPath (+1Iso {n = n}) ^ (suc n))
lem n = lem' n (suc n)

t : (n  : ℕ) → isoToEquiv (+1Iso {n = n}) ≡ idEquiv _
t n = {!!}

iso=refl : (n : ℕ) → isoToPath (+1Iso {n = n}) ^ (suc n) ≡ refl
iso=refl = {!uaIdEquiv!}

later : (n : ℕ) → cong (S¹-cod n) (intLoop (pos n) ∙ loop) ≡ refl
later = {!!}

cod : (n : ℕ) → B-Z/ (suc n) → Type₀
cod n = recB-Z/ (suc n) (S¹-cod n) (later n)

-- elimB-Z/

S¹-dec : {n : ℕ}(x : S¹) → cod n [ x ] → Path (B-Z/ (suc n)) [ base ] [ x ]
S¹-dec base p i = [ (intLoop (pos (fst p))) i ]
S¹-dec {n = n} (loop i) = h i
  where
  help : (x : Fin (suc n)) → fst (transport (λ i → cod n [ loop (~ i) ]) x) ≡ (fst ((-/ 1f) +/ x))
  help x = cong (λ x → fst ((-/ 1f) +/ x)) (transportRefl x)

  help2 : (x : Fin (suc n)) → transport (λ i → Path (B-Z/ (suc n)) [ base ] [ loop i ]) (λ i → [ intLoop (pos (fst ((-/ 1f) +/ x))) i ]) ≡ λ i → [ intLoop (pos (suc (fst ((-/ 1f) +/ x)))) i ]
  help2 x = fromPathP (compPath-filler {ℓ-zero} {B-Z/ (suc n)} (λ i → [ intLoop (pos (fst ((-/ 1f) +/ x))) i ]) (λ i → [ loop i ]))
          ∙ sym (congFunct [_] (intLoop (pos (fst ((-/ 1f) +/ x)))) loop)

  help3 : {!!}
  help3 = {!!}

  h : PathP (λ i → cod n [ loop i ] → [ base ] ≡ [ loop i ]) (λ p i → [ (intLoop (pos (fst p)) i) ]) (λ p i → [ (intLoop (pos (fst p)) i) ])
  h = toPathP
    (funExt λ x → cong (transport (λ i → Path (B-Z/ (suc n)) [ base ] [ loop i ])) (λ i j → [ intLoop (pos (help x i)) j ])
                ∙∙ help2 x
                ∙∙ {!!})

open import Cubical.HITs.Truncation renaming (elim to trElim ; rec to trRec)

B-Z/-trunc : {!!}
B-Z/-trunc = {!!}

set→refl : ∀ {ℓ} (n : ℕ) {A : (x : _) → cod n x → Type ℓ} → (f : (x : S¹) → (s : cod n [ x ]) → A [ x ] s)
         → (x : _) (y : _) → A x y
set→refl n {A = A} f = elimB-Z/ _ f {!!}
  where
  P : cong f (intLoop (pos n) ∙ loop) ≡ {!!}
  P = {!!}

  z : {!transpor !}
  z = {!!}

  m : PathP
      (λ i →
         PathP (λ j → (y : cong (cong (cod n)) kill i j) → A (kill i j) y) (f base)
         (f base))
      (cong f (intLoop (pos n) ∙ loop)) (λ _ → f base)
  m i j s = hcomp (λ k → λ {(i = i0) → {!f ((intLoop (pos n) ∙ loop) j) s!} ; (i = i1) → {!f ((intLoop (pos n) ∙ loop) j) s!} ; (j = i0) → {!!} ; (j = i1) → {!f base!}}) {!!}


dec : (n : ℕ) (x : B-Z/ (suc n)) → cod n x → [ base ] ≡ x
dec n [ base ] p i = [ (intLoop (pos (fst p)) i) ]
dec n [ loop i ] = h i -- h i
  where
  help : (x : Fin (suc n)) → fst (transport (λ i → cod n [ loop (~ i) ]) x) ≡ (fst ((-/ 1f) +/ x))
  help x = cong (λ x → fst ((-/ 1f) +/ x)) (transportRefl x)

  help2 : (x : Fin (suc n)) → transport (λ i → Path (B-Z/ (suc n)) [ base ] [ loop i ]) (λ i → [ intLoop (pos (fst ((-/ 1f) +/ x))) i ]) ≡ λ i → [ intLoop (pos (suc (fst ((-/ 1f) +/ x)))) i ]
  help2 x = fromPathP (compPath-filler {ℓ-zero} {B-Z/ (suc n)} (λ i → [ intLoop (pos (fst ((-/ 1f) +/ x))) i ]) (λ i → [ loop i ]))
          ∙ sym (congFunct [_] (intLoop (pos (fst ((-/ 1f) +/ x)))) loop)

  help3 : {!!}
  help3 = {!!}

  h : PathP (λ i → cod n [ loop i ] → [ base ] ≡ [ loop i ]) (λ p i → [ (intLoop (pos (fst p)) i) ]) (λ p i → [ (intLoop (pos (fst p)) i) ])
  h = toPathP
    (funExt λ x → cong (transport (λ i → Path (B-Z/ (suc n)) [ base ] [ loop i ])) (λ i j → [ intLoop (pos (help x i)) j ])
                ∙∙ help2 x
                ∙∙ {!!})
dec n (kill i i₁) p = {!!}


dec'--trunc : (n : ℕ) (x : B-Z/ (suc n)) → cod n x → (hLevelTrunc 2 ([ base ] ≡ x ))
dec'--trunc n = elimB-Z/ _ (λ x c → ∣ dec n [ x ] c ∣)
                           (isProp→PathP (λ _ → isOfHLevelPathP' 1 (isSetΠ (λ _ → isOfHLevelTrunc 2)) _ _) _ _)

isSet-cod : (n : ℕ) (x : B-Z/ (suc n)) → isSet (cod n x)
isSet-cod = {!!}

enc-trunc : (n : ℕ) → (x : B-Z/ (suc n)) → (Path (hLevelTrunc 3 _) ∣ [ base ] ∣ ∣ x ∣) → cod n x
enc-trunc n x p = {!? ∙∙ ? ∙∙ ?!}

enc-dec : {!!}
enc-dec = {!!}

dec-enc : {!!}
dec-enc = {!!}


{-
ℤ/'_ : (n : ℕ) → Type₀
ℤ/' n = Int / λ x b → (pos n + x) ≡ b


add_ : (b : ℕ) → Int → Int
(add n) m = (pos n) + m

{-
pos+ : (n a : ℕ) → pos (n + a) ≡ (pos n + pos a)
pos+ n zero = cong pos (+-comm n zero)
pos+ n (suc a) = cong pos (+-suc n a) ∙ cong sucInt (pos+ n a)

pos- : (n a : ℕ) → pos ((add n) a) - pos n ≡ pos (idfun ℕ a)
pos- n a = (λ i → pos+ n a i - pos n)
        ∙∙ (λ i → (+-comm (pos n) (pos a) i) - pos n)
        ∙∙ plusMinus (pos n) (pos a)
-}

data ℤ/_ (n : ℕ) : Type₀ where
  [_] : Int → ℤ/ n
  kill-l : (x : Int) → [ pos n + x ] ≡ [ x ]
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Empty renaming (rec to ⊥-rec)

_≤_ : (z y : Int) → Type₀
_≤_ z y = Σ[ n ∈ ℕ ] z + pos n ≡ y

_<_ : (z y : Int) → Type₀
_<_ z y = Σ[ n ∈ ℕ ] pos (suc n) + z ≡ y

dec≤ : (x y : Int) → (y ≤ x) ⊎ (x < y)
dec≤ (pos zero) (pos zero) = inl (0 , refl)
dec≤ (pos zero) (pos (suc m)) = inr (m , refl)
dec≤ (pos (suc n)) (pos zero) = inl ((suc n) , +-comm 0 (pos (suc n)))
dec≤ (pos (suc n)) (pos (suc m)) with dec≤ (pos n) (pos m)
... | inl p = inl ((fst p) , sym (sucInt+ (pos m) (pos (fst p))) ∙ cong sucInt (snd p))
... | inr p = inr ((fst p) , cong sucInt (snd p))
dec≤ (pos n) (negsuc m) = inl (m +N (suc n) , {!!})
dec≤ (negsuc n) (pos n₁) = {!!}
dec≤ (negsuc n) (negsuc n₁) = {!!}

private
  lem : (x y x' y' : Int) → (x + y) + (x' + y') ≡ (x + x') + (y + y')
  lem x y x' y' =
       sym (+-assoc x y (x' + y'))
    ∙∙ cong (λ z → x + (y + z)) (+-comm x' y')
    ∙∙ cong (x +_) (+-assoc y y' x')
    ∙∙ cong (x +_) (+-comm (y + y') x')
    ∙∙ +-assoc x x' (y + y')

·-ldistr : (x y z : Int) → x · (y + z) ≡ ((x · y) + (x · z))
·-ldistr (pos zero) y z = refl
·-ldistr (pos (suc n)) y z =
     (λ i → (y + z) + (·-ldistr (pos n) y z i))
     ∙ lem y z (pos n · y) (pos n · z)
·-ldistr (negsuc zero) y z = sym (-distr y z)
·-ldistr (negsuc (suc n)) y z =
     (λ i → -distr y z (~ i) + ·-ldistr (negsuc n) y z i)
   ∙ lem (- y) (- z) (negsuc n · y) (negsuc n · z)

·-rdistr : (x y z : Int) → (y + z) · x ≡ ((y · x) + (z · x))
·-rdistr x y z = ·-comm (y + z) x ∙∙ ·-ldistr x y z ∙∙ cong₂ _+_ (·-comm x y) (·-comm x z)

decEqℕ : (x y : ℕ) → (x ≡ y) ⊎ (¬ x ≡ y)
decEqℕ zero zero = inl refl
decEqℕ zero (suc y) = inr λ p → snotz (sym p)
decEqℕ (suc x) zero = inr snotz
decEqℕ (suc x) (suc y) with decEqℕ x y
... | inl p = inl (cong suc p)
... | inr p = inr λ q → p (cong predℕ q)

decEqInt : (x y : Int) → (x ≡ y) ⊎ (¬ x ≡ y)
decEqInt (pos zero) (pos zero) = inl refl
decEqInt (pos zero) (pos (suc m)) = inr λ p → snotz (sym (injPos {a = zero} {b = suc m} p))
decEqInt (pos (suc n)) (pos zero) = inr λ p → snotz (injPos {a = suc n} {b = zero} p)
decEqInt (pos (suc n)) (pos (suc m)) with decEqInt (pos n) (pos m)
... | inl p = inl (cong pos (cong suc (injPos p)))
... | inr p = inr λ q → p (cong pos (cong predℕ (injPos q)))
decEqInt (pos n) (negsuc n₁) = inr λ p → negsucNotpos _ _ (sym p)
decEqInt (negsuc n) (pos n₁) = inr (negsucNotpos _ _)
decEqInt (negsuc n) (negsuc zero) = {!!}
decEqInt (negsuc zero) (negsuc (suc m)) = inr {!!}
decEqInt (negsuc (suc n)) (negsuc (suc m)) with decEqInt (negsuc n) (negsuc m)
... | inl p = {!!}
... | inr p = {!decEqℕ!}

x≡ : (n : ℕ) → (n ≡ 0) ⊎ (Σ[ m ∈ ℕ ] n ≡ (suc m))
x≡ zero = inl refl
x≡ (suc n) = inr (n , refl)

modh-type : ℕ → Int → Type₀
modh-type n z =
  Σ[ K ∈ (Int × ℕ) ]
      ((pos (snd K) < pos (suc n)))
    × (z ≡ (pos (snd K) + (fst K · pos (suc n))))

help1 : (n m : Int) → (predInt n · m) ≡ (n · m) - m
help1 (pos zero) (pos zero) = refl
help1 (pos zero) (pos (suc n)) = +-comm (negsuc n) 0
help1 (pos zero) (negsuc n) = cong sucInt (+-comm (pos n) 0)
help1 (pos (suc n)) m =
    sym (plusMinus m (pos n · m))
  ∙ cong (_- m) (+-comm (pos n · m) m)
help1 (negsuc n) m = +-comm (- m) (negsuc n · m) ∙ -≡+- (negsuc n · m) m

help : (n m : ℕ) (z : modh-type (suc n) (pos m))
     → (snd (fst z) ≡ (suc n)) ⊎ (¬ snd (fst z) ≡ (suc n))
     → modh-type (suc n) (pos (suc m))
fst (fst (help n m z (inl x))) = (fst (fst z)) + 1
snd (fst (help n m z (inl x))) = 0
fst (snd (help n m z (inl x))) = suc n , refl
snd (snd (help n m z (inl x))) =
     cong sucInt (snd (snd z))
  ∙∙ sucInt+ (pos (snd (fst z))) (fst (fst z) · pos (suc (suc n)))
  ∙∙ cong (_+ (fst (fst z) · pos (suc (suc n)))) (cong pos (cong suc x))
   ∙ +-comm (pos (2 +N n)) (fst (fst z) · pos (2 +N n))
  ∙∙ sym (·-rdistr (pos (2 +N n)) (fst (fst z)) 1)
  ∙∙ +-comm ((fst (fst z) + 1) · pos (2 +N n)) (pos 0)
fst (fst (help n m z (inr x))) = fst (fst z)
snd (fst (help n m z (inr x))) = suc (snd (fst z))
fst (snd (help n m z (inr x))) with x≡ (fst (fst (snd z)))
... | inr p = predℕ (fst (fst (snd z)))
            , ((cong (λ x → sucInt (pos (suc (predℕ x)) + pos (snd (fst z)))) (snd p))
           ∙∙ sucInt+ (pos (suc (fst p))) (pos (snd (fst z)))
           ∙∙ cong (λ x → pos (suc x) + pos (snd (fst z))) (sym (snd p))
            ∙ snd (fst (snd z)))
... | inl p =
      ⊥-rec (x (injPos (+-comm (pos (snd (fst z))) (pos 0)
                      ∙ cong (λ x → pos x + (pos (snd (fst z)))) (sym p)
                     ∙∙ sym (predInt+ (pos (suc (fst (fst (snd z))))) (pos (snd (fst z))))
                     ∙∙ cong predInt (fst (snd z) .snd))))
snd (snd (help n m z (inr x))) = cong sucInt (snd (snd z))
                               ∙ sucInt+ (pos (snd (fst z))) (fst (fst z) · pos (suc (suc n)))

pos+ : (n x : ℕ) → ℕ
pos+ zero x = 0
pos+ (suc n) x with (decEqℕ x n)
... | inl p = 0
... | inr p = suc x

negsuc++ : (n x : ℕ) → ℕ
negsuc++ zero x = 0
negsuc++ (suc n) x with decEqℕ x 0
... | inl p = n
... | inr p = x

_mod_ : (x n : ℕ) → ℕ
x mod zero = 0
zero mod suc n = 0
suc x mod suc n = pos+ (suc n) (x mod (suc n))

_mod'_ : (z : Int) (n : ℕ) → ℕ
_mod'_ z zero = 0
_mod'_ (pos zero) (suc n) = 0
_mod'_ (pos (suc m)) (suc n) = pos+ (suc n) ((pos m) mod' (suc n))
_mod'_ (negsuc zero) (suc n) = n
_mod'_ (negsuc (suc m)) (suc n) = negsuc++ (suc n) ((negsuc m) mod' (suc n))

data ℤ'/ (n : ℕ) : Type₀ where
  [_] : ℕ → ℤ'/ n
  cyc : (x : ℕ) → [ x ] ≡ [ (x mod n)  ]

s : (n : ℕ) → ℤ'/ n → ℕ
s zero x = 0
s (suc n) [ x ] = x mod suc n
s (suc n) (cyc x i) = {!!}

hilfe : (n : ℕ) → (x : ℤ'/ n) → [ s n x ] ≡ x
hilfe zero x = {!!}
hilfe (suc n) [ x ] = sym (cyc x)
hilfe (suc n) (cyc x i) j =
  hcomp (λ k → λ {(i = i0) → cyc x (~ j ∨ ~ k)
                 ; (i = i1) → cyc (x mod suc n) (~ j)
                 ; (j = i0) → {!!} -- [ mod-mod n x i ]
                 ; (j = i1) → cyc x (i ∨ ~ k)})
        {!!}
{-
i = i0 ⊢ cyc x (~ j)
i = i1 ⊢ cyc (x mod suc n) (~ j)
j = i0 ⊢ [ mod-mod n x i ]
j = i1 ⊢ cyc x i
-}

test : (n : ℕ) → isSet (ℤ'/ n)
test n  =
  isOfHLevelRetract 2 (s n) [_] {!!} isSetℕ

isSetℤ' : (n : ℕ) → isSet (ℤ'/ n)
isSetℤ' zero = isProp→isSet {!!}
  where
  helper : isProp (ℤ'/ zero)
  helper [ x ] [ zero ] = cyc x
  helper [ x ] [ suc x₁ ] = cyc x ∙ sym (cyc (suc x₁))
  helper [ x ] (cyc zero i) = {!!}
  helper [ x ] (cyc (suc x₁) i) = {!!}
  helper (cyc x i) y = {!!}
isSetℤ' (suc n) = {!!}

contrZ/1 : isContr (ℤ'/ 1)
fst contrZ/1 = [ 1 ]
snd contrZ/1 [ zero ] = {!!}
snd contrZ/1 [ suc x ] = {!!} ∙ sym (cyc (suc x))
snd contrZ/1 (cyc x i) = {!!}

_+m_ : {n : ℕ} → ℕ → ℕ → ℕ
_+m_ {n = n} x y = {!x +N y!}

modh : (n : ℕ) (z : Int) →
  Σ[ K ∈ (Int × ℕ) ]
   ((pos (snd K) < pos (suc n)))
 × (z ≡ (pos (snd K) + (fst K · pos (suc n))))
modh zero z = (z , 0) , (((0 , refl) , λ i → +-comm (·-comm 1 z i) (pos 0) i))
modh (suc n) (pos zero) = (0 , 0) , (((suc n , refl) , refl))
fst (fst (modh (suc n) (pos (suc m)))) = fst (fst (help n m (modh (suc n) (pos m)) (decEqℕ _ _)))
snd (fst (modh (suc n) (pos (suc m)))) = snd (fst (help n m (modh (suc n) (pos m)) (decEqℕ _ _)))
fst (snd (modh (suc n) (pos (suc m)))) = fst (snd (help n m (modh (suc n) (pos m)) (decEqℕ _ _)))
snd (snd (modh (suc n) (pos (suc m)))) = snd (snd (help n m (modh (suc n) (pos m)) (decEqℕ _ _)))
modh (suc n) (negsuc zero) = {!!}
modh (suc n) (negsuc (suc m)) = help' n m (modh (suc n) (negsuc m)) (decEqℕ _ _)
  where
  help' : (n m : ℕ) (z : modh-type (suc n) (negsuc m))
       → (snd (fst z) ≡ 0) ⊎ (¬ snd (fst z) ≡ 0)
       → modh-type (suc n) (negsuc (suc m))
  fst (fst (help' n m z (inl x))) = fst (fst z) - 1
  snd (fst (help' n m z (inl x))) = suc n
  fst (snd (help' n m z (inl x))) = 0 , cong sucInt (+-comm 1 (pos n))
  snd (snd (help' n m z (inl x))) =
       cong predInt ((snd (snd z))
                 ∙∙ (cong (λ x → pos x + (fst (fst z) · pos (suc (suc n)))) x)
                 ∙∙ (+-comm (pos 0) (fst (fst z) · pos (suc (suc n)))))
    ∙∙ cong predInt (sym (minusPlus (pos (suc (suc n))) ((fst (fst z) · pos (suc (suc n))))))
    ∙∙ cong predInt (+-comm ((fst (fst z) · pos (suc (suc n))) - (pos (suc (suc n)))) (pos (suc (suc n))))
    ∙∙ predInt+ (pos (suc (suc n))) ((fst (fst z) · pos (suc (suc n))) - (pos (suc (suc n))))
    ∙∙ sym (cong (pos (suc n) +_) (help1 (fst (fst z)) (pos (suc (suc n)))))
  help' n m z (inr x) = {!!}



mod_ : (n : ℕ) → ℕ →  ℕ
(mod zero) m = 0
(mod suc zero) zero = 0
(mod suc zero) (suc zero) = 1
(mod suc zero) (suc (suc m)) = (mod suc zero) m
(mod suc (suc n)) m = {!eq/ !}

intAdd : (n : ℕ) → ℕ →  ℕ → ℕ
intAdd zero _ _ = zero
intAdd (suc zero) zero k = k
intAdd (suc zero) (suc zero) zero = 1
intAdd (suc zero) (suc (suc m)) zero = intAdd (suc zero) m zero
intAdd (suc zero) (suc m) (suc k) = intAdd (suc zero) m k
intAdd (suc (suc n)) m k with discreteℕ (intAdd (suc n) m k) n
... | yes p = {!!}
... | no p = {!!}

_divides_ : (x y : Int) → Type₀
_divides_ x y = Σ[ k ∈ Int ] k · x ≡ y

dec-divides' : (x y : Int) → Dec (x divides y)
dec-divides' (pos zero) (pos zero) = yes (0 , refl)
dec-divides' (pos zero) (pos (suc n)) = no λ {(x , p) → {!!}}
dec-divides' (pos zero) (negsuc n) = no {!!}
dec-divides' (pos (suc zero)) y = yes (y , {!refl!})
dec-divides' (pos (suc (suc n))) (pos zero) = yes (0 , refl)
dec-divides' (pos (suc (suc n))) (pos (suc m)) with (dec-divides' (pos (2 +N n)) (pos m))
... | yes (x , k) = no λ {(x2 , k2) → {!!}}
... | no p = yes ({!p!} , {!!})
dec-divides' (pos (suc (suc n))) (negsuc n₁) = {!!}
dec-divides' (negsuc zero) y = yes (- y , {!!})
dec-divides' (negsuc (suc n)) (pos zero) = yes (0 , refl)
dec-divides' (negsuc (suc n)) (pos (suc m)) = {!!}
dec-divides' (negsuc (suc n)) (negsuc m) = {!!}

infixl 30 _,_
infixl 50 ⋆,_
infixr 50 ∣_

finVec : ∀ {ℓ} → ℕ → Type ℓ → Type ℓ
finVec {ℓ} zero A = finVec0
  module _ where
  data finVec0 : Type ℓ where
    ∣_ : A → finVec0 
finVec {ℓ} (suc n) A = finVec>0
  module _ where
  data finVec>0 : Type ℓ where
    _,_ : finVec n A → A → finVec>0

hej2 : finVec 3 Int
hej2 = (((∣ 3) , 2) , 1) , 0


+finVec : ∀ {ℓ} {A : Type ℓ} (+A : A → A → A) (n : ℕ) (x y : finVec n A) → finVec n A
+finVec _+A_ zero (∣ x) (∣ y) = ∣ (x +A y)
+finVec _+A_ (suc n) (x , x2) (y , y2) = +finVec _+A_ n x y , (x2 +A y2)

data transposeVec {ℓ} (n : ℕ) (A : Type ℓ) : Type ℓ where
  [_]ᵗ : finVec n A → transposeVec n A

_×_-matrix : ∀ {ℓ} → (n m : ℕ) → Type ℓ → Type ℓ
_×_-matrix {ℓ} zero m A = Unit*
_×_-matrix {ℓ} (suc n) zero A = Unit*
_×_-matrix {ℓ} (suc zero) (suc m) A =
  transposeVec m A
_×_-matrix {ℓ} (suc (suc n)) (suc zero) A =
  finVec (suc n) A
_×_-matrix {ℓ} (suc (suc n)) (suc (suc m)) A =
  transposeVec (suc n) (finVec (suc m) A)


_ᵗ : ∀ {ℓ} {A : Type ℓ} {n : ℕ} → finVec n A → transposeVec n A
x ᵗ = [ x ]ᵗ

_ᵗ⁻ : ∀ {ℓ} {A : Type ℓ} {n : ℕ} → transposeVec n A → finVec n A 
([ x ]ᵗ) ᵗ⁻ = x

vecProd : ∀ {ℓ} {A : Type ℓ} {n  : ℕ} (∙A : A → A → A) → finVec n A → transposeVec n A → finVec n A
vecProd {n = zero} _∙A_ (∣ x) [ ∣ y ]ᵗ = ∣ (x ∙A y) -- x ∙A y
vecProd {n = suc n} _∙A_ (x , tx) [ y , ty ]ᵗ = (vecProd _∙A_ x [ y ]ᵗ) , (tx ∙A ty) -- vecProd _+A_ _∙A_ x [ y ]ᵗ +A (tx +A ty)

scalarVec : ∀ {ℓ} {A : Type ℓ} {n  : ℕ} (+A ·A : A → A → A) (x : A) → finVec n A
scalarVec {n = zero} +A _∙A_ x = ∣ x
scalarVec {n = suc n} +A _∙A_ x = scalarVec +A _∙A_ x , x


matr-mult : ∀ {ℓ} {A : Type ℓ} (n m l : ℕ)
                  (+A ·A : A → A → A)
                  (M : ((suc n) × (suc m) -matrix) A)
               → ((suc m) × (suc l) -matrix) A → ((suc n) × (suc l) -matrix) A
matr-mult zero zero l _+A_ _∙A_ [ ∣ x ]ᵗ y = [ vecProd _∙A_ (scalarVec _+A_ _∙A_ x) y ]ᵗ
matr-mult zero (suc m) l _+A_ _·_ [ x ]ᵗ S = {!S!}
matr-mult (suc n) m l _+A_ _·_ M S = {!!}

matr : ∀ {ℓ} → ℕ → ℕ → Type ℓ → Type ℓ
matr zero y A = {!!}
matr {ℓ} (suc n) y A = {!!}


data ℤ''/ (n : ℕ) : Type₀ where
  [_]' : ℕ → ℤ''/ n
  RUnit : (x : ℕ) → [ x +N n ]' ≡ [ x ]'

kalaha : ℕ → Type₀
kalaha zero = Unit
kalaha (suc n) = T
  module _ where
  data T : Type₀ where
    [_] : kalaha n → T
    +1 : T



open import Cubical.HITs.S1 hiding (_·_)
data S¹-mod (n : ℕ) : Type₀ where
  [_] : S¹ → S¹-mod n
  coher : cong [_] (intLoop (pos n)) ≡ refl

0k : {n : ℕ} → kalaha n
0k {n = zero} = tt
0k {n = suc n} = [ 0k ]

upBack : (n : ℕ) → kalaha n →  kalaha (suc n)
upBack zero = [_]
upBack (suc n) = [_]

downUnder : (n : ℕ) → kalaha (suc n) → kalaha n
downUnder zero x = _
downUnder (suc n) [ x ] = x
downUnder (suc n) +1 = 0k
open import Cubical.Data.Empty renaming (rec to ⊥-rec)
≠-fib : (n : ℕ) → kalaha (suc n) → Type₀
≠-fib n [ x ] = Unit
≠-fib n +1 = ⊥
open import Cubical.Data.Unit
+1≠[] : {n : ℕ} {x : kalaha n} → ¬ (+1 ≡ [ x ])
+1≠[] {n = n} p = transport (cong (≠-fib n) (sym p)) tt

upBck-downUnder : (n : ℕ) (x : _) → Σ[ y ∈ kalaha n ] x ≡ [ y ] → upBack n (downUnder n x) ≡ x
upBck-downUnder zero [ x ] _ = refl
upBck-downUnder (suc n) [ x ] _ = refl
upBck-downUnder zero +1 (y , p) = ⊥-rec (+1≠[] p)
upBck-downUnder (suc n) +1 (y , p) = ⊥-rec (+1≠[] p)

revFun : (n : ℕ) → (x y : kalaha n) → Path (T n) [ x ] [ y ] → x ≡ y
revFun zero x y _ = refl
revFun (suc n) x y = cong (downUnder (suc n))

jaha : (n : ℕ) (x : kalaha (suc n)) (p1 : _) (p2 : _) → refl  ≡ upBck-downUnder n x p1 ∙∙ refl ∙∙ sym (upBck-downUnder n x p2)
jaha zero [ x ] (x' , p1) (y' , p2) = rUnit refl
jaha (suc n) [ x ] (x' , p1) (y' , p2) = rUnit refl
jaha zero +1 (x' , p1) (y' , p2) = ⊥-rec (+1≠[] p1)
jaha (suc n) +1 (x' , p1) (y' , p2) = ⊥-rec (+1≠[] p1)

retra : (n : ℕ) (x y : kalaha (suc n)) (p : x ≡ y) (p1 : Σ[ a ∈ kalaha n ] x ≡ [ a ]) (p2 : Σ[ b ∈ kalaha n ] y ≡ [ b ])
      → cong (upBack n) (cong (downUnder n) p) ≡ (upBck-downUnder n x p1  ∙∙ p ∙∙ sym (upBck-downUnder n y p2))
retra n x y =
  J (λ y p → (p1 : Σ[ a ∈ kalaha n ] x ≡ [ a ]) (p2 : Σ[ b ∈ kalaha n ] y ≡ [ b ])
           → cong (upBack n) (cong (downUnder n) p) ≡ (upBck-downUnder n x p1  ∙∙ p ∙∙ sym (upBck-downUnder n y p2)))
    (jaha n x)

pathSpaceIso : (n : ℕ) (x y : kalaha n)
            → Iso (x ≡ y) (Path (kalaha (suc n)) [ x ] [ y ])
Iso.fun (pathSpaceIso n x y) p = cong [_] p
Iso.inv (pathSpaceIso n x y) = revFun n _ _
Iso.rightInv (pathSpaceIso zero x y) p =
    retra 0 [ x ] [ y ] p (_ , refl) (_ , refl)
  ∙ sym (rUnit p)
Iso.rightInv (pathSpaceIso (suc n) x y) p =
    retra (suc n) [ x ] [ y ] p (_ , refl) (_ , refl)
  ∙ sym (rUnit p)
Iso.leftInv (pathSpaceIso zero x y) _ = isSetUnit _ _ _ _
Iso.leftInv (pathSpaceIso (suc n) x y) =
  J (λ y p → revFun (suc n) _ _ (cong [_] p) ≡ p) refl

decKalaha : (n : ℕ) → Discrete (kalaha n)
decKalaha zero _ _ = yes refl
decKalaha (suc n) [ x ] [ y ] =
  transport (λ i → Dec (isoToPath (pathSpaceIso n x y) i)) (decKalaha n x y)
decKalaha (suc n) [ x ] +1 = no λ p → ⊥-rec (+1≠[] (sym p))
decKalaha (suc n) +1 [ x ] = no λ p → ⊥-rec (+1≠[] p)
decKalaha (suc n) +1 +1 = yes refl

isSetKalaha : (n : ℕ) → isSet (kalaha n)
isSetKalaha n = Discrete→isSet (decKalaha n)

kalaha-dec : (n : ℕ) → (x y : kalaha n) → (x ≡ y) ⊎ (¬ x ≡ y)
kalaha-dec zero x y = inl refl
kalaha-dec (suc n) [ x ] [ y ] with kalaha-dec n x y
... | inl p = inl (cong [_] p)
... | inr p = inr λ q → p (Iso.inv (pathSpaceIso n x y) q)
kalaha-dec (suc n) [ x ] +1 = inr λ q → +1≠[] (sym q)
kalaha-dec (suc n) +1 [ x ] = inr +1≠[]
kalaha-dec (suc n) +1 +1 = inl refl

_++1 : {n : ℕ}(x : kalaha n) → kalaha n
_++1 {n = zero} x = tt
_++1 {n = suc zero} [ x ] = +1
_++1 {n = suc zero} +1 = [ tt ]
_++1 {n = suc (suc n)} [ [ x ] ] = [ [ x ] ++1 ]
_++1 {n = suc (suc n)} [ +1 ] = +1
_++1 {n = suc (suc n)} +1 = 0k

repr : {n : ℕ} → kalaha n → ℕ
repr {n = zero} x = 0
repr {n = suc n} [ x ] = repr x
repr {n = suc n} +1 = (suc n)






comp^_ : ∀ {ℓ} {A : Type ℓ} → ℕ → (f : A → A) → A → A
(comp^ zero) f x = x
(comp^ (suc n)) f = f ∘ (comp^ n) f

comp'^_ : ∀ {ℓ} {A : Type ℓ} {n : ℕ} → kalaha n → (f : A → A) → A → A
comp'^_ {n = zero} x f a = a
comp'^_ {n = suc n} [ x ] f = comp'^_ x f
comp'^_ {n = suc zero} +1 f = f
comp'^_ {n = suc (suc n)} +1 f = f ∘ comp'^_ {n = (suc n)} +1 f

tc : kalaha 2 -- Z/4
tc = [ +1 ]

rtc = repr tc

Z/ : ℕ → Type₀
Z/ zero = Int
Z/ (suc n) = kalaha n

t-help : (n x : ℕ) (y : Z/ (2 +N n)) → (y ≡ +1) ⊎ (¬ y ≡ +1) → Z/ (2 +N n)
t-help n x y (inl x₁) = 0k
t-help n x y (inr x₁) = y ++1
{-
t : (n : ℕ) → ℕ → Z/ n
t zero x = pos x
t (suc zero) x = 0k
t (suc (suc n)) zero = 0k
t (suc (suc n)) (suc x) =
  t-help n x (t (suc (suc n)) x) (kalaha-dec _ (t (suc (suc n)) x) +1)
-}
{-
h : (n : ℕ) → t 2 (n +N 2) ≡ t 2 n
h = {!? ∙∙ ? ∙∙ ?!}
-}
t : (n x : ℕ) → Z/ n
t zero x = pos x
t (suc n) zero = 0k
t (suc n) (suc x) = t (suc n) x ++1

_+k_ : {n : ℕ} → Z/ n → Z/ n → Z/ n
_+k_ {n = zero} x y = x + y
_+k_ {n = suc n} x y = (comp'^ y) _++1 x

_+k'_ : {n : ℕ} → Z/ n → Z/ n → Z/ n
_+k'_ {n = zero} x y = x + y
_+k'_ {n = suc n} x y = {!!}
open import Cubical.Data.Bool renaming (true to noll ; false to ett)
Z'/ : (n : ℕ) → Type₀
Z'/ zero = Int
Z'/ (suc zero) = Unit
Z'/ (suc (suc zero)) = Bool
Z'/ (suc (suc (suc n))) = kalahi
  module _ where
  data kalahi : Type₀ where
    zero : kalahi
    mid : Z'/ (suc n) → kalahi
    mx : kalahi

0k' : {n : ℕ} → Z'/ n
0k' {n = zero} = 0
0k' {n = suc zero} = tt
0k' {n = suc (suc zero)} = noll
0k' {n = suc (suc (suc n))} = zero

1k' : {n : ℕ} → Z'/ n
1k' {n = zero} = 1
1k' {n = suc zero} = tt
1k' {n = suc (suc zero)} = ett
1k' {n = suc (suc (suc n))} = mid 0k'

succ : {n : ℕ} → Z'/ n → Z'/ n
succ {n = zero} x = sucInt x
succ {n = suc zero} x = _
succ {n = suc (suc zero)} ett = noll
succ {n = suc (suc zero)} noll = ett
succ {n = suc (suc (suc zero))} zero = mid tt
succ {n = suc (suc (suc zero))} (mid x) = mx
succ {n = suc (suc (suc zero))} mx = zero
succ {n = suc (suc (suc (suc zero)))} zero = mid noll
succ {n = suc (suc (suc (suc zero)))} (mid ett) = mx
succ {n = suc (suc (suc (suc zero)))} (mid noll) = mid ett
succ {n = suc (suc (suc (suc zero)))} mx = zero
succ {n = suc (suc (suc (suc (suc n))))} zero = mid zero
succ {n = suc (suc (suc (suc (suc n))))} (mid zero) = mid (mid 0k')
succ {n = suc (suc (suc (suc (suc n))))} (mid (mid x)) = mid (succ (mid x))
succ {n = suc (suc (suc (suc (suc n))))} (mid mx) = mx
succ {n = suc (suc (suc (suc (suc n))))} mx = zero


{-
ZZ/ : (n : ℕ) → Type₀
ZZ/ zero = Int
ZZ/ (suc zero) = Unit
ZZ/ (suc (suc n)) = {!!}
  module _ hej : Type₀ where
    [_] : ZZ/ n → hej
    +1  ZZ/ n
-}


-- data ΩP {A B C : Type₀} (a₀ : A) (b₀ : B) (f : A → B) (g : C → B) : Type₀ where
--   inll : a₀ ≡ a₀ → ΩP a₀ b₀ f g
--   inrr : b₀ ≡ b₀ → ΩP a₀ b₀ f g

-- ΩPush : {!(f y : → ?) → ?!}
-- ΩPush = {!!}

-- z/ : (n : ℕ) → Type₀
-- z/ zero = Int
-- z/ (suc n) = Pushout {A = Bool × Int} {B = Int} {C = Int}
--                      (λ {(noll , c) → c ; (ett , c) → c + pos (suc n)})
--                      λ {(x , c) → c}

-- _z/+_ : {n : ℕ} → z/ n → z/ n → z/ n
-- _z/+_ {n = n} x y = {!!}


-- {-
-- _z/+_ : {n : ℕ} → z/ n → z/ n → z/ n
-- _z/+_ {n = zero} x y = x + y
-- _z/+_ {n = suc n} (inl x) y = y
-- _z/+_ {n = suc n} (inr x) (inl x₁) = inr x
-- _z/+_ {n = suc n} (inr x) (inr x₁) = inr (x + x₁)
-- _z/+_ {n = suc n} (inr x) (push a i) = helpz a x n i
--   where
--   helpz : (a x : Int) (n : ℕ) → Path (z/ (suc n)) (inr x) (inr (x + (a · pos (suc n))))
--   helpz (pos zero) x n = refl
--   helpz (pos (suc zero)) (pos zero) n = sym (push 0) ∙∙ push 1 ∙∙ λ i → inr (+-comm (pos (suc n)) 0 i) -- λ i → inr (sucInt (+-comm 0 (pos (suc n)) (~ i)))
--   helpz (pos (suc zero)) (pos (suc zero)) zero = {!!}
--   helpz (pos (suc zero)) (pos (suc zero)) (suc n) = {!!} ∙∙ {!!} ∙∙ {!!}
--   helpz (pos (suc zero)) (pos (suc (suc n₁))) n = {!!}
--   helpz (pos (suc zero)) (negsuc n₁) n = {!!}
--   helpz (pos (suc (suc n₁))) x n = {!!}
--    -- ({!cong inr (sym (sucInt+ x (pos n))))!} ∙ {!helpz 1 ? ?!}) ∙∙ helpz (pos n₁) (sucInt (x +pos n)) n ∙∙ sym (cong inr (+-assoc x (pos (suc n)) (pos n₁ · pos (suc n))))
--   helpz (negsuc m) x n = {!!}
-- _z/+_ {n = suc n} (push a i) y = {!!}
-- -}

-- pres : {n : ℕ} → Z'/ n
-- pres {n = n} = {!!}

-- M : {n : ℕ} → Z'/ n
-- M {n = zero} = - 1
-- M {n = suc zero} = _
-- M {n = suc (suc zero)} = ett
-- M {n = suc (suc (suc n))} = mx

-- _+k''_ : {n : ℕ} → Z'/ n → Z'/ n → Z'/ n
-- _+k''_ {n = zero} x y = x + y
-- _+k''_ {n = suc zero} x y = _
-- _+k''_ {n = suc (suc zero)} ett ett = noll
-- _+k''_ {n = suc (suc zero)} ett noll = ett
-- _+k''_ {n = suc (suc zero)} noll y = y
-- _+k''_ {n = suc (suc (suc n))} zero y = y
-- _+k''_ {n = suc (suc (suc n))} (mid x) y = {!!}
-- _+k''_ {n = suc (suc (suc n))} mx y = {!!}

-- repr0≡0 : {n : ℕ} → (repr {n = n}) 0k ≡ 0
-- repr0≡0 {n = zero} = refl
-- repr0≡0 {n = (suc n)} = repr0≡0 {n = n}

-- repr^ : (n : ℕ) (y : kalaha n) →  (comp'^ y) _++1 0k ≡ y
-- repr^-help : (n : ℕ) (y : kalaha n) → Path (kalaha (suc n)) ((comp'^ y) _++1 [ 0k ]) [ y ]
-- repr^-help zero y = refl
-- repr^-help (suc n) [ x ] = {!!}
-- repr^-help (suc n) +1 = {!!}
-- repr^ zero y = refl
-- repr^ (suc n) [ x ] = repr^-help n x
-- repr^ (suc zero) +1 = refl
-- repr^ (suc (suc n)) +1 = {!repr^-help (suc n) +1!}



-- hlp : (n : ℕ) (y x : _) → Path (kalaha n) ((comp'^ y) _++1 x ++1) ((comp'^ y) _++1 (x ++1))
-- hlp zero y x = refl
-- hlp (suc n) [ x₁ ] [ x ] = {!!}
-- hlp (suc n) +1 [ x ] = {!!}
-- hlp (suc n) [ x ] +1 = {!!}
-- hlp (suc zero) +1 +1 = refl
-- hlp (suc (suc n)) +1 +1 = {!!}

-- t-hom : (n x y : ℕ) → t (suc n) (x +N y) ≡ (t (suc n) x) +k (t (suc n) y)
-- t-hom zero zero zero = refl
-- t-hom (suc n) zero zero = {!!}
-- t-hom n zero (suc y) = cong _++1 (t-hom n zero y) ∙ {!!} -- sym (repr^ _ ((t (suc n) y ++1)))
-- t-hom n (suc x) y = cong _++1 (t-hom n x y) ∙ hlp _ (t (suc n) y) (t (suc n) x)

-- t-add0 : (x n : ℕ) → t (suc (suc n)) (x +N suc (suc n)) ≡ t (suc (suc n)) x
-- t-add0 zero zero = refl
-- t-add0 zero (suc n) = {!!} -- ({!!} ∙ {!!}) ∙ refl {x = 0k}
-- t-add0 (suc x) n = cong _++1 (t-add0 x n)

-- _mod''_ : (x n : ℕ) → ℕ
-- x mod'' zero = x
-- x mod'' suc n = repr (t (suc n) x)


-- ka : (n : ℕ) → ℤ''/ (suc n) → Z/ (suc n)
-- ka zero x = tt
-- ka (suc n) [ x ]' = t (2 +N n) x
-- ka (suc n) (RUnit x i) = {!!}

-- -- (comp'^ y) _++1 x

-- -- _1-- : {n : ℕ}(x : kalaha n) → kalaha n
-- -- _1-- {n = n} x = (comp^ n) _++1 x

-- -- _-k_ : {n : ℕ} → kalaha n → kalaha n → kalaha n
-- -- _-k_ {n = n} x y = (comp'^ y) _1-- x

-- -- c : kalaha 3
-- -- c = +1 +k +1

-- -- comp^-helper' : {n : ℕ} (x : kalaha (2 +N n)) (y : kalaha n) → (comp^ repr x) (_++1 {n = (2 +N n)}) [ [ y ] ] ≡ (({![ (comp^ repr x) (_++1 {n = (1 +N n)}) [ y ] ] !} ++1) ++1)
-- -- comp^-helper' {n = zero} [ [ x ] ] y = refl
-- -- comp^-helper' {n = zero} [ +1 ] y = refl
-- -- comp^-helper' {n = suc n} [ x ] y = {!!}
-- -- comp^-helper' {n = zero} +1 y = {!refl!}
-- -- comp^-helper' {n = suc n} +1 y = {!refl!}


-- -- open import Cubical.Data.Sum
-- -- comp^-helper : {n : ℕ} (x y : kalaha n) → (comp'^ y) _++1 x ≡ (comp'^ x) _++1 y
-- -- comp^-helper {n = zero} x y = refl
-- -- comp^-helper {n = suc zero} [ x ] [ x₁ ] = refl
-- -- comp^-helper {n = suc zero} [ x ] +1 = refl
-- -- comp^-helper {n = suc zero} +1 [ x ] = refl
-- -- comp^-helper {n = suc zero} +1 +1 = refl
-- -- comp^-helper {n = suc (suc n)} [ x ] [ y ] = {!y!}
-- --   where
  
-- --   help : {n : ℕ} (x : _) (y : _) → ((comp'^ y) (_++1 {n = suc (suc n)}) [ x ] ≡ [ (comp'^_ {n = (suc n)} y) (_++1 {n = suc n}) x ])
-- --       ⊎ ((comp'^ y) (_++1 {n = suc (suc n)}) [ x ] ≡ +1)
-- --   help {n = zero} [ x ] [ x₁ ] = inl refl
-- --   help {n = zero} [ x ] +1 = inl refl
-- --   help {n = zero} +1 [ x ] = inl refl
-- --   help {n = zero} +1 +1 = inr refl
-- --   help {n = suc n} [ x ] [ y ] with (help x y)
-- --   ... | inr p = inl ({!p!} ∙∙ {!!} ∙∙ λ i → [ p (~ i) ])
-- --   ... | inl p = {!p!}
-- --   help {n = suc n} [ x ] +1 = {!!}
-- --   help {n = suc n} +1 y = {!!}
-- -- comp^-helper {n = suc (suc n)} [ x ] +1 = {!!}
-- -- comp^-helper {n = suc (suc n)} +1 y = {!!}


-- -- _∙k_ : {n : ℕ} → kalaha n → kalaha n → kalaha n
-- -- _∙k_ {n = zero} = λ _ _ → tt
-- -- _∙k_ {n = suc n} x y = (comp^ repr y) (λ y → x +k y) y

-- -- +k-comm : {n : ℕ} → (x y : kalaha n) → x +k y ≡ y +k x
-- -- +k-comm {n = zero} x y = refl
-- -- +k-comm {n = suc zero} [ x ] [ x₁ ] = refl
-- -- +k-comm {n = suc zero} [ x ] +1 = refl
-- -- +k-comm {n = suc zero} +1 [ x ] = refl
-- -- +k-comm {n = suc zero} +1 +1 = refl
-- -- +k-comm {n = suc (suc n)} [ x ] [ y ] = {!!}
-- -- +k-comm {n = suc (suc n)} [ x ] +1 = {!!}
-- -- +k-comm {n = suc (suc n)} +1 y = {!!}


-- -- help : (n : ℕ) → kalaha n → Int
-- -- help zero x = 0
-- -- help (suc n) [ x ] = help n x
-- -- help (suc n) +1 = pos (suc n)

-- -- isSet-kalaha : ℕ → Type₀
-- -- isSet-kalaha = {!!}

-- -- dec-divides : (x y : Int) → Dec (x divides y)
-- -- dec-divides (pos zero) (pos zero) = yes (0 , refl)
-- -- dec-divides (pos (suc n)) (pos zero) = yes (0 , refl)
-- -- dec-divides (pos zero) (pos (suc m)) = {!!}
-- -- dec-divides (pos (suc n)) (pos (suc m)) with (dec-divides (pos (suc n)) (pos m))
-- -- ... | yes (x , k) = yes {!!}
-- -- ... | no p = {!!}
-- -- dec-divides (pos n) (negsuc n₁) = {!!}
-- -- dec-divides (negsuc n) y = {!!}

-- -- ℤ/→ℤ/' : (n : ℕ) → ℤ/ n → ℤ/' n
-- -- ℤ/→ℤ/' n [ x ] = [ x ]
-- -- ℤ/→ℤ/' n (kill-l x i) = (eq/ x (pos n + x) refl) (~ i)

-- -- ℤ/'ℤ : (n : ℕ) → Int
-- -- ℤ/'ℤ n = {!!}

-- -- -- ℤ/_ : (n : ℕ) → Type₀
-- -- -- ℤ/ n = Pushout (add n) (idfun _)

-- -- -- ℤ/→ℕ : (n : ℕ) → ℤ/ n → Int
-- -- -- ℤ/→ℕ n (inl x) = pos x - pos n
-- -- -- ℤ/→ℕ n (inr x) = pos x
-- -- -- ℤ/→ℕ n (push a i) = pos- n a i

-- -- -- ℕ→ℤ/ : (n : ℕ) → Int → ℤ/ n
-- -- -- ℕ→ℤ/ n (pos m) = inr m
-- -- -- ℕ→ℤ/ n (negsuc m) = inr m

-- -- -- toPropElim : ∀ {ℓ} (n : ℕ) → {A : ℤ/ n → Type ℓ}
-- -- --      → ((x : _) → isProp (A x))
-- -- --      → ((n : ℕ) → A (inl n))
-- -- --      → (x : _) → A x
-- -- -- toPropElim n prop f (inl x) = f x
-- -- -- toPropElim n {A = A} prop f (inr x) = transport (cong A (push x)) (f (n + x))
-- -- -- toPropElim n {A = A} prop f (push a i) =
-- -- --   isProp→PathP {B = λ i → A (push a i)} (λ _ → prop _)
-- -- --                 (f (n + a)) (transport (cong A (push a)) (f (n + a))) i 

-- -- -- open import Cubical.Relation.Nullary

-- -- -- decEqℤ/ : (n : ℕ) → Discrete (ℤ/ n)
-- -- -- decEqℤ/ n =
-- -- --   toPropElim n (λ _ → isPropΠ λ _ → isPropDec {!!}) {!!}

-- -- -- -+hom : (x n : _) → ℕ→ℤ/ (suc n) (pos x +negsuc n) ≡ inr x
-- -- -- -+hom x n = {!!}

-- -- -- -hom : (x n : _) → ℕ→ℤ/ n (pos x - pos n) ≡ ℕ→ℤ/ n (pos x)
-- -- -- -hom x zero = refl
-- -- -- -hom x (suc n) = -+hom x n

-- -- -- q : (x n : _) → Path (ℤ/ n) (inl ((add n) x)) (inl x)
-- -- -- q x zero = refl
-- -- -- q x (suc n) = {!!}

-- -- -- p : (x n : _) → ℕ→ℤ/ n (pos x - pos n) ≡ inl x
-- -- -- p x n = -hom x n ∙∙ sym (push x) ∙∙ {!!}

-- -- -- test : (n : ℕ) → (x : ℤ/ n) → ℕ→ℤ/ n (ℤ/→ℕ n x) ≡ x
-- -- -- test n (inl x) = p x n
-- -- -- test n (inr x) =
-- -- --   transport (λ i → ℕ→ℤ/ n (pos- n x i) ≡ push x i) (p ((add n) x) n)
-- -- -- test n (push x i) j =
-- -- --   transp (λ z → ℕ→ℤ/ n (pos- n x (i ∧ z)) ≡ push x (i ∧ z)) (~ i) (p ((add n) x) n) j

-- -- -- isSet-ℤ/ : (n : ℕ) → isSet (ℤ/ n)
-- -- -- isSet-ℤ/ n =
-- -- --   isSetRetract (ℤ/→ℕ n)
-- -- --                (ℕ→ℤ/ n)
-- -- --                (test n)
-- -- --                isSetInt

-- -- -- -- S : ℕ₋₁ → Type₀
-- -- -- -- S neg1 = ⊥
-- -- -- -- S (ℕ→ℕ₋₁ n) = Susp (S (-1+ n))

-- -- -- -- S₊ : ℕ → Type₀
-- -- -- -- S₊ 0 = Bool
-- -- -- -- S₊ 1 = S¹
-- -- -- -- S₊ (suc (suc n)) = Susp (S₊ (suc n))

-- -- -- -- ptSn : (n : ℕ) → S₊ n
-- -- -- -- ptSn zero = true
-- -- -- -- ptSn (suc zero) = base
-- -- -- -- ptSn (suc (suc n)) = north

-- -- -- -- -- Pointed version
-- -- -- -- S₊∙ : (n : ℕ) → Pointed₀
-- -- -- -- S₊∙ n = (S₊ n) , ptSn n
-}

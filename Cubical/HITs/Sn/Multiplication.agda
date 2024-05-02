{-# OPTIONS --safe #-}
module Cubical.HITs.Sn.Multiplication where

open import Cubical.Foundations.Pointed

open import Cubical.Foundations.Path
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Univalence
open import Cubical.HITs.S1 renaming (_·_ to _*_ ; rec to S¹Fun) hiding (elim)
open import Cubical.HITs.S2 renaming (S¹×S¹→S² to S¹×S¹→S²')
open import Cubical.HITs.S3
open import Cubical.Data.Nat hiding (elim)
open import Cubical.Data.Sigma
open import Cubical.HITs.Sn.Base
open import Cubical.HITs.Susp renaming (toSusp to σ)
open import Cubical.HITs.Truncation
open import Cubical.HITs.Join renaming (joinS¹S¹→S³ to joinS¹S¹→S3)
open import Cubical.Data.Bool hiding (elim)

open import Cubical.HITs.Sn.Properties


open import Cubical.HITs.Pushout
open import Cubical.HITs.SmashProduct
open import Cubical.Homotopy.Loopspace

open import Cubical.Foundations.Pointed.Homogeneous

open import Cubical.Data.Sum

open Iso



open PlusBis
open import Cubical.HITs.Susp.Properties
open import Cubical.HITs.Join

-- move/rename
σS : {n : ℕ} → S₊ n → Path (S₊ (suc n)) (ptSn _) (ptSn _)
σS {n = zero} false = loop
σS {n = zero} true = refl
σS {n = suc n} x = σ (S₊∙ _) x

IsoSucSphereSusp∙' : (n : ℕ)
  → Iso.fun (IsoSucSphereSusp n) (ptSn (suc n)) ≡ north
IsoSucSphereSusp∙' zero = refl
IsoSucSphereSusp∙' (suc n) = refl

-- multiplication
sphereFun↑ : {n m k : ℕ}
  → (f : S₊ n → S₊ m → S₊ k)
  → S₊ (suc n) → S₊ m → S₊ (suc k)
sphereFun↑ {n = zero} {m = m} f base y = ptSn _
sphereFun↑ {n = zero} {m = m} f (loop i) y = σS (f false y) i
sphereFun↑ {n = suc n} {m = m} f north y = ptSn _
sphereFun↑ {n = suc n} {m = m} f south y = ptSn _
sphereFun↑ {n = suc n} {m = m} f (merid a i) y = σS (f a y) i

_⌣S_ : {n m : ℕ} → S₊ n → S₊ m → S₊ (n + m)
_⌣S_ {n = zero} {m = m} false y = y
_⌣S_ {n = zero} {m = m} true y = ptSn m
_⌣S_ {n = suc n} {m = m} = sphereFun↑ (_⌣S_ {n = n})

-- Left- and right-unit laws
IdR⌣S : {n m : ℕ} (y : S₊ m)
  → Path (S₊ (n + m)) (ptSn n ⌣S y) (ptSn (n + m))
IdR⌣S {n = zero} {m = m} y = refl
IdR⌣S {n = suc zero} {m = m} y = refl
IdR⌣S {n = suc (suc n)} {m = m} y = refl

IdL⌣S : {n m : ℕ} (x : S₊ n)
  → Path (S₊ (n + m)) (x ⌣S (ptSn m)) (ptSn (n + m))
IdL⌣S {n = zero} false = refl
IdL⌣S {n = zero} true = refl
IdL⌣S {n = suc zero} base = refl
IdL⌣S {n = suc zero} {zero} (loop i) j = base
IdL⌣S {n = suc zero} {suc m} (loop i) j = rCancel (merid (ptSn (suc m))) j i
IdL⌣S {n = suc (suc n)} {m} north j = north
IdL⌣S {n = suc (suc n)} {m} south j = north
IdL⌣S {n = suc (suc n)} {m} (merid a i) j =
  (cong (σ (S₊∙ (suc (n + m)))) (IdL⌣S a)
  ∙ rCancel (merid (ptSn _))) j i

IdL⌣S≡IdR⌣S : (n m : ℕ)
  → IdL⌣S {n = n} {m = m} (ptSn n) ≡ IdR⌣S (ptSn m)
IdL⌣S≡IdR⌣S zero m = refl
IdL⌣S≡IdR⌣S (suc zero) m = refl
IdL⌣S≡IdR⌣S (suc (suc n)) m = refl

-- Goal: graded commutativity

-- To state it: we'll need iterated negations
-S^ : {k : ℕ} (n : ℕ) → S₊ k → S₊ k
-S^ zero x = x
-S^ (suc n) x = invSphere (-S^ n x)

-- The folowing is an explicit definition of -S^ (n · m) which is
-- often easier to reason about
-S^-expl : {k : ℕ} (n m : ℕ)
  → isEvenT n ⊎ isOddT n
  → isEvenT m ⊎ isOddT m
  → S₊ k → S₊ k
-S^-expl {k = zero} n m (inl x₁) q x = x
-S^-expl {k = zero} n m (inr x₁) (inl x₂) x = x
-S^-expl {k = zero} n m (inr x₁) (inr x₂) false = true
-S^-expl {k = zero} n m (inr x₁) (inr x₂) true = false
-S^-expl {k = suc zero} n m p q base = base
-S^-expl {k = suc zero} n m (inl x) q (loop i) = loop i
-S^-expl {k = suc zero} n m (inr x) (inl x₁) (loop i) = loop i
-S^-expl {k = suc zero} n m (inr x) (inr x₁) (loop i) = loop (~ i)
-S^-expl {k = suc (suc k)} n m p q north = north
-S^-expl {k = suc (suc k)} n m p q south = north
-S^-expl {k = suc (suc k)} n m (inl x) q (merid a i) = σ (S₊∙ (suc k)) a i
-S^-expl {k = suc (suc k)} n m (inr x) (inl x₁) (merid a i) =
  σ (S₊∙ (suc k)) a i
-S^-expl {k = suc (suc k)} n m (inr x) (inr x₁) (merid a i) =
  σ (S₊∙ (suc k)) a (~ i)

--  invSphere commutes with S^
invSphere-S^ : {k : ℕ} (n : ℕ) (x : S₊ k)
  → invSphere (-S^ n x) ≡ -S^ n (invSphere x)
invSphere-S^ zero x = refl
invSphere-S^ (suc n) x = cong invSphere (invSphere-S^ n x)

-S^² : {k : ℕ} (n : ℕ) (x : S₊ k) → -S^ n (-S^ n x) ≡ x
-S^² zero x = refl
-S^² (suc n) x =
  cong invSphere (sym (invSphere-S^ n (-S^ n x)))
  ∙ invSphere² _ (-S^ n (-S^ n x))
  ∙ -S^² n x

-S^Iso : {k : ℕ} (n : ℕ) → Iso (S₊ k) (S₊ k)
fun (-S^Iso n) = -S^ n
inv (-S^Iso n) = -S^ n
rightInv (-S^Iso n) = -S^² n
leftInv (-S^Iso n) = -S^² n

-S^-comp : {k : ℕ} (n m : ℕ) (x : S₊ k)
  → -S^ n (-S^ m x) ≡ -S^ (n + m) x
-S^-comp zero m x = refl
-S^-comp (suc n) m x = cong invSphere (-S^-comp n m x)

-S^·2 : {k : ℕ} (n : ℕ) (x : S₊ k) → -S^ (n + n) x ≡ x
-S^·2 zero x = refl
-S^·2 (suc n) x =
    cong invSphere (λ i → -S^ (+-comm n (suc n) i) x)
  ∙ invSphere² _ (-S^ (n + n) x)
  ∙ -S^·2 n x

-- technical transport lemma
private
  -S^-transp : {k : ℕ} (m : ℕ) (p : k ≡ m) (n : ℕ) (x : S₊ k)
    → subst S₊ p (-S^ n x) ≡ -S^ n (subst S₊ p x)
  -S^-transp =
    J> λ n x → transportRefl _
              ∙ sym (cong (-S^ n) (transportRefl x))

-- Iterated path inversion
sym^ : ∀ {ℓ} {A : Type ℓ} {x : A} (n : ℕ) → x ≡ x → x ≡ x
sym^ zero p = p
sym^ (suc n) p = sym (sym^ n p)

-- Interaction between -S^ and sym^
σS-S^ : {k : ℕ} (n : ℕ) (x : S₊ (suc k))
  → σS (-S^ n x) ≡ sym^ n (σS x)
σS-S^ {k = k} zero x = refl
σS-S^ {k = k} (suc n) x =
  σ-invSphere k _ ∙ cong sym (σS-S^ n x)

sphereFun↑-subst : {n m : ℕ} (k' k : ℕ) (p : k' ≡ k)
  → (f : S₊ n → S₊ m → S₊ k') (x : S₊ _) (y : S₊ _)
  → sphereFun↑ (λ x y → subst S₊ p (f x y)) x y
   ≡ subst S₊ (cong suc p) (sphereFun↑ f x y)
sphereFun↑-subst k' = J> λ f x y
  → (λ i → sphereFun↑ (λ x₁ y₁ → transportRefl (f x₁ y₁) i) x y)
   ∙ sym (transportRefl _)

sphereFun↑-invSphere : {n m k : ℕ}
  → (f : S₊ (suc n) → S₊ (suc m) → S₊ (suc k)) (x : S₊ _) (y : S₊ _)
  → sphereFun↑ (λ x y → invSphere' (f x y)) x y
   ≡ invSphere' (sphereFun↑ (λ x y → (f x y)) x y)
sphereFun↑-invSphere {n = n} {m = m} {k = k} f north y = refl
sphereFun↑-invSphere {n = n} {m = m} {k = k} f south y = refl
sphereFun↑-invSphere {n = n} {m = m} {k = k} f (merid a i) y j =
  lem k (f a y) j i
  where
  lem : (k : ℕ) (x : S₊ (suc k))
    → (σS (invSphere' x)) ≡ (cong invSphere' (σS x))
  lem k x =
    sym (cong-∙ invSphere' (merid x) (sym (merid (ptSn _)))
      ∙∙ cong (cong invSphere' (merid x) ∙_)
          (rCancel (merid (ptSn _)))
      ∙∙ (sym (rUnit _)
        ∙ sym (σ-invSphere k x)
        ∙ cong (σ (S₊∙ (suc k)))
           (sym (invSphere'≡ x))))

sphereFun↑^ : {n m k : ℕ} (l : ℕ)
  → (f : S₊ (suc n) → S₊ (suc m) → S₊ (suc k)) (x : S₊ _) (y : S₊ _)
  → sphereFun↑ (λ x y → -S^ l (f x y)) x y
   ≡ -S^ l (sphereFun↑ (λ x y → (f x y)) x y)
sphereFun↑^ zero f x y = refl
sphereFun↑^ (suc l) f x y =
    (λ i → sphereFun↑ (λ x₁ y₁ → invSphere'≡ (-S^ l (f x₁ y₁)) (~ i)) x y)
  ∙ sphereFun↑-invSphere (λ x₁ y₁ → (-S^ l (f x₁ y₁))) x y
  ∙ invSphere'≡ ((sphereFun↑ (λ x₁ y₁ → -S^ l (f x₁ y₁)) x y))
  ∙ cong invSphere (sphereFun↑^ l f x y)

S^-even : {k : ℕ} (n : ℕ) (x : S₊ k) → isEvenT n → -S^ n x ≡ x
S^-even zero x p = refl
S^-even (suc (suc n)) x p = invSphere² _ (-S^ n x) ∙ S^-even n x p

move-transp-S^ : {k : ℕ} (n : ℕ) (p : k ≡ n) (m : ℕ)
  → (x : S₊ k) (y : S₊ n)
  → subst S₊ p (-S^ m x) ≡ y
  → subst S₊ (sym p) (-S^ m y) ≡ x
move-transp-S^ =
  J> λ m x → J> transportRefl _
  ∙ cong (-S^ m) (transportRefl _)
  ∙ -S^² m x

master-lem : ∀ {ℓ} {A : Type ℓ} {x : A} (p : x ≡ x) (coh : refl ≡ p)
  (q : p ≡ p)
  → Cube (λ j k → coh j (~ k)) (λ j k → coh j (~ k))
          (λ i k → q k i) (λ i k → q i (~ k))
          (λ j k → coh (~ k) j) λ j k → coh (~ k) j
master-lem = J> λ q → λ i j k → sym≡flipSquare q j (~ k) i

gr-comm-l : {m : ℕ} → (x : S¹) (y : S₊ (suc m))
  → (x ⌣S y)
   ≡ subst S₊ (+-comm (suc m) 1)
           (-S^ (suc m) (y ⌣S x))
gr-comm-l {m = zero} x y = (main x y ∙ invSphere'≡ (y ⌣S x)) ∙ sym (transportRefl (invSusp (y ⌣S x)))
  where
  pp-main : (x : S¹) → PathP (λ i → IdL⌣S {m = 1} x i
          ≡ IdL⌣S {m = 1} x i) (cong (x ⌣S_) loop) (sym (σ (S₊∙ _) x))
  pp-main base i j = rCancel (merid base) (~ i) (~ j) 
  pp-main (loop k) i j = master-lem _ (sym (rCancel (merid base))) (λ j k → σ (S₊∙ 1) (loop j) k) k i j

  pp-help : (x : S¹) → PathP (λ i → IdL⌣S {m = 1} x i
          ≡ IdL⌣S {m = 1} x i) (cong (x ⌣S_) loop) (cong invSphere' (σ (S₊∙ _) x))
  pp-help x = pp-main x
    ▷ (rUnit _
    ∙∙ cong (sym (σ (S₊∙ _) x) ∙_) (sym (rCancel (merid base)))
    ∙∙ sym (cong-∙ invSphere' (merid x) (sym (merid base))))

  main : (x y : S¹) → (x ⌣S y) ≡ invSphere' (y ⌣S x)
  main x base = IdL⌣S {m = 1} x
  main x (loop i) = flipSquare (pp-help x) i
gr-comm-l {m = suc m} x y =
    (main-lem x y
   ∙ sym (transportRefl (invSphere' (sphereFun↑ (λ x₂ x₃ → x₃ ⌣S x₂) y x)))
  ∙ sym (compSubstℕ {A = S₊} (cong suc (sym (+-comm (suc m) 1))) (+-comm (suc (suc m)) 1) refl
     {x = invSphere' (sphereFun↑ (λ x₂ x₃ → x₃ ⌣S x₂) y x)}))
  ∙ cong (subst S₊ (+-comm (suc (suc m)) 1))
      (cong (subst S₊ (cong suc (sym (+-comm (suc m) 1))))
        (sym (S^-lem (suc m) (sphereFun↑ (λ x₂ x₃ → x₃ ⌣S x₂) y x)))
      ∙ -S^-transp _ (cong suc (sym (+-comm (suc m) 1)))
         (suc (suc m) + suc m)
         (sphereFun↑ (λ x₂ x₃ → x₃ ⌣S x₂) y x)
      ∙ sym (-S^-comp (suc (suc m)) (suc m)
         (subst S₊ (cong suc (sym (+-comm (suc m) 1)))
           (sphereFun↑ (λ x₂ x₃ → x₃ ⌣S x₂) y x))))
  ∙ cong (subst S₊ (+-comm (suc (suc m)) 1)
       ∘ -S^ (suc (suc m)))
       ((sym (-S^-transp _ (cong suc (sym (+-comm (suc m) 1))) (suc m) (sphereFun↑ (λ x₂ x₃ → x₃ ⌣S x₂) y x))
       ∙ cong (subst S₊ (cong suc (sym (+-comm (suc m) 1))))
             (sym (sphereFun↑^ (suc m)
              (λ x₂ x₃ →  (x₃ ⌣S x₂)) y x))
       ∙ sym (sphereFun↑-subst _ _ (sym (+-comm (suc m) 1))
         (λ x₂ x₃ →  (-S^ (suc m) (x₃ ⌣S x₂))) y x))
       ∙ cong (λ (s : S₊ (suc m) → S¹ → S₊ (suc m + 1))
                → sphereFun↑ s y x)
               (refl
             ∙ sym (funExt λ x → funExt λ y
             → sym (move-transp-S^ _ (+-comm (suc m) 1)
             (suc m) (x ⌣S y) (y ⌣S x)
              (sym (gr-comm-l y x)))
             ∙ refl)))
  where
  S^-lem : {k : ℕ} (m : ℕ) (x : S₊ k)
    → -S^ (suc m + m) x ≡ invSphere' x
  S^-lem m x =
       sym (invSphere'≡ (-S^ (m + m) x))
     ∙ cong invSphere' (-S^·2 m x)

  pst : +-comm (suc (suc m)) 1
      ∙ cong suc (sym (+-comm (suc m) 1)) ≡ refl
  pst = isSetℕ _ _ _ _

  ⌣S-south : (x : S¹) → x ⌣S south ≡ north
  ⌣S-south base = refl
  ⌣S-south (loop i) j =
    (cong (σ (S₊∙ _)) (sym (merid (ptSn (suc m))) )
    ∙ rCancel (merid (ptSn _))) j i


  PathP-main : (x : S¹) (a : S₊ (suc m))
    → PathP (λ i → IdL⌣S x i ≡ ⌣S-south x i) (cong (x ⌣S_) (merid a))
        (sym (σ (S₊∙ _) (x ⌣S a))) 
  PathP-main base a j i = rCancel (merid north) (~ j) (~ i)
  PathP-main (loop k) a j i =
    hcomp (λ r → λ {(i = i0) → rCancel (merid north) j k
                   ; (i = i1) → compPath-filler' (cong (σ (S₊∙ (suc (suc m)))) (sym (merid (ptSn (suc m))))) (rCancel (merid north)) r j k
                   ; (j = i0) → σ (S₊∙ (suc (suc m))) (compPath-filler (merid a) (sym (merid (ptSn (suc m)))) (~ r) i) k
                   ; (j = i1) → σ (S₊∙ (suc (suc m))) (σ (S₊∙ (suc m)) a k) (~ i)
                   ; (k = i0) → rCancel (merid north) (~ j) (~ i)
                   ; (k = i1) → rCancel (merid north) (~ j) (~ i)})
          (master-lem _ (sym (rCancel (merid north)))
           (λ i k → σ (S₊∙ (suc (suc m))) (loop i ⌣S a) k) k j i)

  pp : (x : S¹) (a : S₊ (suc m))
    → PathP (λ i → IdL⌣S x i ≡ ⌣S-south x i) (cong (x ⌣S_) (merid a))
        (cong invSphere' (σ (S₊∙ _) (x ⌣S a))) 
  pp x a = PathP-main x a
      ▷ (rUnit _
     ∙∙ cong (sym (σ (S₊∙ _) (x ⌣S a)) ∙_) (sym (rCancel (merid north)))
     ∙∙ sym (cong-∙ invSphere' (merid (x ⌣S a)) (sym (merid north))))

  main-lem : (x : S¹) (y : S₊ (2 + m))
    → (x ⌣S y)
      ≡ invSphere' (sphereFun↑ (λ x₂ x₃ → x₃ ⌣S x₂) y x)
  main-lem x north = IdL⌣S x
  main-lem x south = ⌣S-south x
  main-lem x (merid a i) j = pp x a j i

gr-comm-lem : {n m : ℕ}
  → ((x : S₊ (suc n)) (y : S₊ (suc (suc m)))
     → (x ⌣S y) ≡ subst S₊ (+-comm (suc (suc m)) (suc n)) (-S^ (suc (suc m) · (suc n)) (y ⌣S x)))
  → (((x : S₊ (suc m)) (y : S₊ (suc (suc n)))
     → (x ⌣S y) ≡ subst S₊ (+-comm (suc (suc n)) (suc m)) (-S^ ((suc (suc n)) · (suc m)) (y ⌣S x))))
  → (((x : S₊ (suc n)) (y : S₊ (suc m))
     → (y ⌣S x) ≡ subst S₊ (sym (+-comm (suc m) (suc n))) (-S^ ((suc n) · (suc m)) (x ⌣S y))))
  → (x : S₊ (suc (suc n))) (y : S₊ (suc (suc m)))
  → (x ⌣S y) ≡ subst S₊ (+-comm (suc (suc m)) (suc (suc n))) (-S^ (suc (suc m) · (suc (suc n))) (y ⌣S x))
gr-comm-lem {n = n} {m = m} ind1 ind2 ind3 x y =
     cong (λ (s : S₊ (suc n) → S₊ (suc (suc m)) → S₊ ((suc n) + (suc (suc m)))) → sphereFun↑ s x y)
          (funExt (λ x → funExt λ y
          → ind1 x y))
  ∙ (sphereFun↑-subst _ _ (+-comm (suc (suc m)) (suc n)) (λ x y → -S^ (suc (suc m) · suc n) (y ⌣S x)) x y
  ∙ cong (subst S₊ (cong suc (+-comm (suc (suc m)) (suc n))))
      (sphereFun↑^ (suc (suc m) · suc n)  (λ x y → y ⌣S x) x y
      ∙ cong (-S^ (suc (suc m) · suc n))
         (cong (λ (s : S₊ (suc n) → S₊ (suc (suc m)) → S₊ ((suc (suc m)) + (suc n))) → sphereFun↑ s x y)
           (funExt (λ x → funExt λ y →
            cong (λ (s : S₊ (suc m) → S₊ (suc n) → S₊ ((suc m) + (suc n))) → sphereFun↑ s y x)
             (funExt λ x
                    → funExt λ y
                     → ind3 y x)
          ∙ sphereFun↑-subst _ _ (sym (+-comm (suc m) (suc n)))
              (λ x y → -S^ (suc n · suc m) (y ⌣S x)) y x
          ∙ cong (subst S₊ (cong suc (sym (+-comm (suc m) (suc n)))))
                 (sphereFun↑^ (suc n · suc m) (λ x y → (y ⌣S x)) y x
                ∙ cong (-S^ (suc n · suc m) )
                   refl)
          ∙ refl))
          ∙ sphereFun↑-subst _ _  (sym (cong suc (+-comm (suc m) (suc n))))
              ((λ x₁ x₂ →
               (-S^ (suc n · suc m) (sphereFun↑ (λ x₃ y₁ → y₁ ⌣S x₃) x₂ x₁)))) x y
          ∙ cong (subst S₊ (sym (cong (suc ∘ suc) (+-comm (suc m) (suc n)))))
                   ((sphereFun↑^ (suc n · suc m)
                     ((λ x₁ x₂ → (sphereFun↑ (λ x₃ y₁ → y₁ ⌣S x₃) x₂ x₁))) x y
                  ∙ cong (-S^ (suc n · suc m)) (cool x y))))
          ∙ refl)
  ∙ big-lem (suc n) (suc m)
      _ (λ i → suc (suc (+-comm (suc m) (suc n) (~ i))))
      _ (λ i → suc (+-comm (suc (suc m)) (suc n) i)) _
      (sym (+-comm (suc (suc m)) (suc (suc n))))
      (λ i → suc (+-comm (suc (suc n)) (suc m) i))
      (sphereFun↑ (λ x₁ y₂ → y₂ ⌣S x₁) y x)
  ∙ sym (cong (subst S₊ (+-comm (suc (suc m)) (suc (suc n))))
         (cong (-S^ (suc (suc m) · suc (suc n)))
          ((λ i → sphereFun↑ (λ x y → ind2 x y i) y x)
         ∙ sphereFun↑-subst _ _
             (+-comm (suc (suc n)) (suc m)) (λ x y → -S^ (suc (suc n) · suc m) (y ⌣S x)) y x
         ∙ cong (subst S₊ (cong suc (+-comm (suc (suc n)) (suc m))))
            (sphereFun↑^ (suc (suc n) · suc m) (λ x y → y ⌣S x) y x
            ∙ refl)))))
    where
    ℕ-p : (n m : ℕ)
      → (suc m · suc n + suc n · m)
       ≡ (m + m) + ((n · m + n · m) + (suc n))
    ℕ-p n m =
      cong suc (cong (_+ (m + n · m)) (cong (n +_) (·-comm m (suc n)))
             ∙ sym (+-assoc n (m + n · m) _)
             ∙ +-comm n _
             ∙ cong (_+ n) (+-assoc (m + n · m) m (n · m)
                         ∙ cong (_+ (n · m))
                              (sym (+-assoc m (n · m) m)
                            ∙ cong (m +_) (+-comm (n · m) m)
                            ∙ +-assoc m m (n · m))
                            ∙ sym (+-assoc (m + m) (n · m) (n · m))))
      ∙ sym (+-suc (m + m + (n · m + n · m)) n)
      ∙ sym (+-assoc (m + m) (n · m + n · m) (suc n))

    ℕ-p2 : (n m : ℕ) → suc m · n + n · m + 1 ≡ (((n · m) + (n · m)) + (suc n))
    ℕ-p2 n m = (λ _ → ((n + m · n) + n · m) + 1)
      ∙ cong (_+ 1) (sym (+-assoc n (m · n) (n · m))
                    ∙ (λ i → +-comm n ((·-comm m n i) + n · m) i)
                    ∙ refl)
      ∙ sym (+-assoc (n · m + n · m) n 1)
      ∙ cong (n · m + n · m +_) (+-comm n 1)

    big-lem : (n m : ℕ) {x : ℕ} (y : ℕ) (p : x ≡ y) (z : ℕ) (s : y ≡ z)
              (d : ℕ) (r : z ≡ d) (t : x ≡ d)
       (a : S₊ x)
      → subst S₊ s (-S^ (suc m · n) (subst S₊ p (-S^ (n · m) (invSphere' a))))
      ≡ subst S₊ (sym r)
          (-S^ (suc m · suc n)
           (subst S₊ t (-S^ (suc n · m) a)))
    big-lem n m =
      J> (J> (J> λ t a
      → transportRefl _
      ∙ cong (-S^ (n + m · n)) (transportRefl _)
      ∙ sym (transportRefl _
           ∙ cong (-S^ (suc m · suc n)) ((λ i → subst S₊ (isSetℕ _ _ t refl i) (-S^ (m + n · m) a))
               ∙ transportRefl (-S^ (m + n · m) a) )
           ∙ -S^-comp (suc m · suc n) (suc n · m) a
           ∙ ((funExt⁻ (cong -S^ (ℕ-p n m)) a
             ∙ (sym (-S^-comp (m + m) _ a)
              ∙ -S^·2 m (-S^ (n · m + n · m + suc n) a))
             ∙ funExt⁻ (cong -S^ (sym (ℕ-p2 n m))) a)
            ∙ sym (-S^-comp (suc m · n + n · m) 1 a)
            ∙ cong (-S^ (suc m · n + n · m))
               (sym (invSphere'≡ a)))
           ∙ sym (-S^-comp (suc m · n) (n · m) (invSphere' a)) )))

    l1 : (x :  S₊ (2 + n))
      → sphereFun↑ (λ x₂ x₃ → sphereFun↑ (λ x₄ y₁ → y₁ ⌣S x₄) x₃ x₂) x north ≡ north
    l1 north = refl
    l1 south = refl
    l1 (merid a i) j = rCancel (merid north) j i

    l2 : (x :  S₊ (2 + n))
      → sphereFun↑ (λ x₂ x₃
        → sphereFun↑ (λ x₄ y₁ → y₁ ⌣S x₄) x₃ x₂) x south
        ≡ north
    l2 north = refl
    l2 south = refl
    l2 (merid a i) j = rCancel (merid north) j i

    cool : (x : S₊ (2 + n)) (y : S₊ (2 + m))
       → (sphereFun↑ (λ x₁ x₂
          → sphereFun↑ (λ x₃ y₁ → y₁ ⌣S x₃) x₂ x₁) x y)
        ≡ invSphere' (sphereFun↑ (λ x₁ y₂ → y₂ ⌣S x₁) y x)
    cool x north = l1 x
    cool x south = l2 x
    cool x (merid a i) j = h j i
      where
      main : (x : _) → PathP (λ i → l1 x i ≡ l2 x i)
             (cong (sphereFun↑ (λ x₂ x₃
              → sphereFun↑ (λ x₄ y₁ → y₁ ⌣S x₄) x₃ x₂) x )
               (merid a))
             (sym (σ (S₊∙ (suc (suc (n + suc m)))) (x ⌣S a)))
      main north = cong sym (sym (rCancel (merid north)))
      main south = cong sym (sym (rCancel (merid north)))
      main (merid z i) j k =
        master-lem _
          (sym (rCancel (merid north)))
          (cong (λ x → σ (S₊∙ (suc (suc (n + suc m))))
           (x ⌣S a)) (merid z)) i j k

      h : PathP (λ i → l1 x i ≡ l2 x i)
                (cong (sphereFun↑
                 (λ x₂ x₃ → sphereFun↑ (λ x₄ y₁ → y₁ ⌣S x₄) x₃ x₂) x)
                  (merid a)) (cong invSphere' (σ (S₊∙ _) (x ⌣S a)))
      h = main x
        ▷ ((rUnit _ ∙ cong (sym (σ (S₊∙ _) (x ⌣S a)) ∙_)
            (sym (rCancel (merid north))))
           ∙ sym (cong-∙ invSphere'
              (merid (x ⌣S a)) (sym (merid (ptSn _)))))

⌣S-comm₀ : (x : Bool) (m : ℕ) (y : S₊ m)
  → PathP (λ i → S₊ (+-zero m (~ i))) (x ⌣S y) (y ⌣S x)
⌣S-comm₀ false =
  elim+2 (λ { false → refl ; true → refl})
    (λ { base → refl ; (loop i) → refl})
    ind
  where
  ind : (n : ℕ) →
      ((y : S₊ (suc n)) →
       PathP (λ i → S₊ (suc (+-zero n (~ i)))) y (y ⌣S false)) →
      (y : Susp (S₊ (suc n))) →
      PathP (λ i → Susp (S₊ (suc (+-zero n (~ i))))) y (y ⌣S false)
  ind n p north i = north
  ind n p south i = merid (ptSn (suc (+-zero n (~ i)))) (~ i)
  ind n p (merid a j) i =
    comp (λ k → Susp (S₊ (suc (+-zero n (~ i ∨ ~ k)))))
         (λ r →
         λ {(i = i0) → merid a j
          ; (i = i1) →
            σ (S₊∙ (suc (+-zero n (~ r)))) (p a r) j
          ; (j = i0) → north
          ; (j = i1) → merid (ptSn (suc (+-zero n (~ i ∨ ~ r)))) (~ i)})
         (compPath-filler (merid a) (sym (merid (ptSn _))) i j)
⌣S-comm₀ true m y = (λ i → ptSn (+-zero m (~ i))) ▷ (sym (IdL⌣S y))

⌣S-comm : {n m : ℕ} (x : S₊ n) (y : S₊ m)
  → (x ⌣S y) ≡ subst S₊ (+-comm m n) (-S^ (m · n) (y ⌣S x))
⌣S-comm {n = zero} {m = m} x y =
  sym (fromPathP (symP {A = λ i → S₊ (+-zero m i)} ((⌣S-comm₀ x m y))))
  ∙ sym (cong (subst S₊ (+-zero m))
        ((λ i → -S^ (0≡m·0 m (~ i)) (y ⌣S x))))
⌣S-comm {n = suc n} {m = zero} x y =
  sym (fromPathP (⌣S-comm₀ y (suc n) x))
  ∙ (λ i → subst S₊ (isSetℕ _ _
             (sym (+-comm (suc n) zero))
             (+-comm zero (suc n)) i) (y ⌣S x))
⌣S-comm {n = suc zero} {m = suc m} x y =
    gr-comm-l x y
  ∙ cong (subst S₊ (+-comm (suc m) 1))
     λ i → -S^ (·-identityʳ (suc m) (~ i)) (y ⌣S x)
⌣S-comm {n = suc (suc n)} {m = suc zero} x y =
    sym (substSubst⁻ S₊ (+-comm 1 (suc (suc n))) (x ⌣S y))
  ∙ cong (subst S₊ (+-comm 1 (suc (suc n))))
        ((λ i → subst S₊ (isSetℕ _ _
           (sym (+-comm 1 (suc (suc n)))) (+-comm (suc (suc n)) 1) i)
           (x ⌣S y))
      ∙ (sym (sym
         (-S^-transp _ (+-comm (suc (suc n)) 1) (1 · suc (suc n))
           (-S^ (suc (suc n)) (x ⌣S y)))
            ∙ cong (subst S₊ (+-comm (suc (suc n)) 1))
               (cong (-S^ (1 · suc (suc n)))
                 (λ i → -S^ (·-identityˡ (suc (suc n)) (~ i)) (x ⌣S y))
              ∙ -S^² (1 · suc (suc n)) (x ⌣S y)))))
  ∙ sym (cong (subst S₊ (+-comm 1 (suc (suc n)))
             ∘ -S^ (1 · suc (suc n))) (gr-comm-l y x))
⌣S-comm {n = suc (suc n)} {m = suc (suc m)} x y =
  gr-comm-lem ⌣S-comm ⌣S-comm
    (λ x y → (sym (cong (subst S₊ (sym (+-comm (suc m) (suc n))))
               (sym (-S^-transp _ (+-comm (suc m) (suc n))
                 (suc n · suc m) (-S^ (suc m · suc n) (y ⌣S x)))
             ∙ cong (subst S₊ (+-comm (suc m) (suc n)))
                (cong (-S^ (suc n · suc m))
                    (λ i → -S^ (·-comm (suc m) (suc n) i) (y ⌣S x))
                  ∙ -S^² (suc n · suc m) (y ⌣S x) ))
            ∙ subst⁻Subst S₊ (+-comm (suc m) (suc n)) (y ⌣S x) ))
      ∙ sym (cong (subst S₊ (sym (+-comm (suc m) (suc n)))
                 ∘ -S^ (suc n · suc m))
         (⌣S-comm x y))) x y


⋀S∙ : (n m : ℕ) → (S₊∙ n ⋀∙ S₊∙ m) →∙ (S₊∙ (n + m))
fst (⋀S∙ n m) (inl x) = ptSn _
fst (⋀S∙ n m) (inr x) = (fst x) ⌣S (snd x)
fst (⋀S∙ n m) (push (inl x) i) = IdL⌣S x (~ i)
fst (⋀S∙ n m) (push (inr x) i) = IdR⌣S x (~ i)
fst (⋀S∙ n m) (push (push a i₁) i) = IdL⌣S≡IdR⌣S n m i₁ (~ i)
snd (⋀S∙ n m) = refl

⋀S : (n m : ℕ) → (S₊∙ n ⋀ S₊∙ m) → (S₊ (n + m))
⋀S n m = fst (⋀S∙ n m)

module _ {ℓ ℓ' : Level} {A : Pointed ℓ} {B : Pointed ℓ'} where
  merid-fill : typ A → I → I → I → Susp (A ⋀ B)
  merid-fill a i j k =
    hfill (λ k → λ {(i = i0) → north
                   ; (i = i1) → merid (push (inl a) k) j
                   ; (j = i0) → north
                   ; (j = i1) → merid (inl tt) i})
          (inS (merid (inl tt) (i ∧ j))) k

  inl-fill₁ : typ A → I → I → I → (Susp∙ (typ A)) ⋀ B
  inl-fill₁ a i j k =
    hfill (λ k → λ {(i = i0) → inl tt
                   ; (i = i1) → inr (σ A a j , snd B)
                   ; (j = i0) → push (push tt k) i
                   ; (j = i1) → push (push tt k) i})
           (inS (push (inl (σ A a j)) i)) k

  inl-fill : typ A → I → I → I → (Susp∙ (typ A)) ⋀ B
  inl-fill a i j k =
    hfill (λ k → λ {(i = i0) → inl tt
                   ; (i = i1) → doubleCompPath-filler
                                   (push (inr (snd B)))
                                   (λ i₂ → inr (σ A a i₂ , snd B))
                                   (sym (push (inr (snd B)))) k j
                   ; (j = i0) → push (inr (snd B)) (~ k ∧ i)
                   ; (j = i1) → push (inr (snd B)) (~ k ∧ i)})
          (inS (inl-fill₁ a i j i1)) k

  inr-fill₁ : typ B → I → I → I → (Susp∙ (typ A)) ⋀ B
  inr-fill₁ b i j k =
    hfill (λ k → λ {(i = i0) → inl tt
                   ; (i = i1) → inr (rCancel (merid (pt A)) (~ k) j , b)
                   ; (j = i0) → push (inr b) i
                   ; (j = i1) → push (inr b) i})
          (inS (push (inr b) i)) k

  inr-fill : typ B → I → I → I → (Susp∙ (typ A)) ⋀ B
  inr-fill b i j k =
    hfill (λ k → λ {(i = i0) → inl tt
                   ; (i = i1) → doubleCompPath-filler
                                   (push (inr b))
                                   (λ i₂ → inr (σ A (pt A) i₂ , b))
                                   (sym (push (inr b))) k j
                   ; (j = i0) → push (inr b) (~ k ∧ i)
                   ; (j = i1) → push (inr b) (~ k ∧ i)})
          (inS (inr-fill₁ b i j i1)) k

  SuspL→Susp⋀ : (Susp∙ (typ A)) ⋀ B → Susp (A ⋀ B)
  SuspL→Susp⋀ (inl x) = north
  SuspL→Susp⋀ (inr (north , y)) = north
  SuspL→Susp⋀ (inr (south , y)) = south
  SuspL→Susp⋀ (inr (merid a i , y)) = merid (inr (a , y)) i
  SuspL→Susp⋀ (push (inl north) i) = north
  SuspL→Susp⋀ (push (inl south) i) = merid (inl tt) i
  SuspL→Susp⋀ (push (inl (merid a j)) i) = merid-fill a i j i1
  SuspL→Susp⋀ (push (inr x) i) = north
  SuspL→Susp⋀ (push (push a i₁) i) = north

  Susp⋀→SuspL : Susp (A ⋀ B) → (Susp∙ (typ A)) ⋀ B
  Susp⋀→SuspL north = inl tt
  Susp⋀→SuspL south = inl tt
  Susp⋀→SuspL (merid (inl x) i) = inl tt
  Susp⋀→SuspL (merid (inr (x , y)) i) = (push (inr y) ∙∙ (λ i → inr (toSusp A x i , y)) ∙∙ sym (push (inr y))) i
  Susp⋀→SuspL (merid (push (inl x) i₁) i) = inl-fill x i₁ i i1
  Susp⋀→SuspL (merid (push (inr x) i₁) i) = inr-fill x i₁ i i1
  Susp⋀→SuspL (merid (push (push a k) j) i) =
    hcomp (λ r → λ {(i = i0) → inl-fill (snd A) j i r
                   ; (i = i1) → inr-fill (snd B) j i r
                   ; (j = i0) → inl tt
                   ; (j = i1) → doubleCompPath-filler
                                   (push (inr (pt B)))
                                   (λ i₂ → inr (σ A (pt A) i₂ , (pt B)))
                                   (sym (push (inr (pt B)))) r i
                   ; (k = i0) → inl-fill (snd A) j i r
                   ; (k = i1) → inr-fill (snd B) j i r})
      (hcomp (λ r → λ {(i = i0) → push (push tt (r ∨ k)) j
                      ; (i = i1) → push (push tt (r ∨ k)) j
                      ; (j = i0) → inl tt -- inl tt
                      ; (j = i1) → inr (rCancel (merid (pt A)) (~ r ∧ k) i , pt B)
                      ; (k = i0) → inl-fill₁ (snd A) j i r
                      ; (k = i1) → inr-fill₁ (snd B) j i r})
         (hcomp (λ r → λ {(i = i0) → push (push tt k) j
                         ; (i = i1) → push (push tt k) j
                         ; (j = i0) → inl tt
                         ; (j = i1) → inr (rCancel (merid (pt A)) (~ r ∨ k) i , pt B)
                         ; (k = i0) → push (inl (rCancel (merid (pt A)) (~ r) i)) j
                         ; (k = i1) → push (inr (snd B)) j})
                   (push (push tt k) j)))

  SuspSmashCommIso : Iso (Susp∙ (typ A) ⋀ B) (Susp (A ⋀ B))
  fun SuspSmashCommIso = SuspL→Susp⋀
  inv SuspSmashCommIso = Susp⋀→SuspL
  rightInv SuspSmashCommIso north = refl
  rightInv SuspSmashCommIso south = merid (inl tt)
  rightInv SuspSmashCommIso (merid a i) j =
    hcomp (λ r → λ {(i = i0) → north
                   ; (i = i1) → merid (inl tt) (j ∧ r)
                   ; (j = i0) → f₁≡f₂ (~ r) .fst a i
                   ; (j = i1) → compPath-filler
                                  (merid a) (sym (merid (inl tt))) (~ r) i })
           (f₂ .fst a i)
    where
    f₁ f₂ : (A ⋀∙ B) →∙ Ω (Susp∙ (A ⋀ B))
    fst f₁ x = cong SuspL→Susp⋀ (cong Susp⋀→SuspL (merid x))
    snd f₁ = refl
    fst f₂ = toSusp (A ⋀∙ B)
    snd f₂ = rCancel (merid (inl tt))

    inr' : (Susp (typ A)) × (typ B) → (Susp∙ (typ A)) ⋀ B
    inr' = inr

    f₁≡f₂ : f₁ ≡ f₂
    f₁≡f₂ =
      ⋀→∙Homogeneous≡ (isHomogeneousPath _ _)
            λ x y
         →  cong (cong SuspL→Susp⋀) (cong (push (inr y) ∙∙_∙∙ sym (push (inr y)))
              (cong-∙ (λ x → inr' (x , y)) (merid x) (sym (merid (pt A)))))
         ∙∙ cong-∙∙ SuspL→Susp⋀ (push (inr y))
              (cong (λ x → inr' (x , y)) (merid x)
             ∙ cong (λ x → inr' (x , y)) (sym (merid (pt A)))) (sym (push (inr y)))
            ∙∙ (sym (rUnit _)
             ∙ cong-∙ SuspL→Susp⋀
                (λ i → inr' (merid x i , y)) (λ i → inr' (merid (pt A) (~ i) , y))
             ∙ cong (merid (inr (x , y)) ∙_)
                λ j i → merid (push (inr y) (~ j)) (~ i) )
  leftInv SuspSmashCommIso =
    ⋀-fun≡ _ _ refl
      (λ x → main (snd x) (fst x))
      (λ { north i j → sₙ i j i1
         ; south i j → sₛ i j i1
         ; (merid a k) i j → cube a j k i})
      λ x i j → push (inr x) (i ∧ j)
    where
    inr' : Susp (typ A) × (typ B) → (Susp∙ (typ A)) ⋀ B
    inr' = inr
    sₙ : I → I → I → (Susp∙ (typ A)) ⋀ B
    sₙ i j k =
      hfill (λ k → λ {(i = i0) → inl tt
                     ; (i = i1) → push (inr (pt B)) (j ∨ ~ k)
                     ; (j = i0) → push (inr (pt B)) (i ∧ ~ k)
                     ; (j = i1) → push (inl north) i})
            (inS (push (push tt (~ j)) i))
            k

    sₛ : I → I → I → (Susp∙ (typ A)) ⋀ B
    sₛ i j k =
      hfill (λ k → λ {(i = i0) → inl tt
                     ; (i = i1) → compPath-filler
                                    (push (inr (pt B)))
                                    (λ i → inr (merid (pt A) i , pt B)) k j
                     ; (j = i0) → inl tt
                     ; (j = i1) → push (inl (merid (pt A) k)) i})
            (inS (sₙ i j i1))
            k

    filler : fst A → fst B → I → I → I → (Susp∙ (typ A)) ⋀ B
    filler a y i j k =
      hfill (λ k → λ {(i = i0) → push (inr y) j
                     ; (i = i1) → compPath-filler
                                    (push (inr y))
                                    (λ i₁ → inr (merid (pt A) i₁ , y)) k j
                     ; (j = i0) → Susp⋀→SuspL (SuspL→Susp⋀ (inr (merid a i , y)))
                     ; (j = i1) → inr (compPath-filler (merid a) (sym (merid (pt A))) (~ k) i , y)})
            (inS (doubleCompPath-filler
                   (push (inr y))
                   (λ i₁ → inr' (σ A a i₁ , y))
                   (sym (push (inr y))) (~ j) i)) k

    cube₁ : (a : typ A)
      → Cube (λ k i → inv SuspSmashCommIso (merid-fill a k i i1))
              (λ k i → inl-fill a k i i1)
              (λ _ _ → inl tt)
              refl
              (λ _ _ → inl tt)
              λ _ _ → inl tt
    cube₁ a j k i =
      hcomp (λ r → λ {(i = i0) → inl tt
                     ; (i = i1) → inl tt
                     ; (j = i0) → inv SuspSmashCommIso (merid-fill a k i r)
                     ; (j = i1) → inl-fill a k i i1
                     ; (k = i0) → inl tt
                     ; (k = i1) → inl-fill a (j ∨ r) i i1})
             (inl-fill a (j ∧ k) i i1)

    cube : (a : typ A)
      → Cube (λ k i → inv SuspSmashCommIso
                         (fun SuspSmashCommIso (push (inl (merid a k)) i)))
              (λ k i → push (inl (merid a k)) i)
              (λ j i → sₙ i j i1) (λ j i → sₛ i j i1)
              (λ j k → inl tt) (λ j k → filler a (pt B) k j i1)
    cube a = (λ j k i → cube₁ a j i k) ◁
     (λ j k i →
      hcomp (λ r
        → λ {(i = i0) → inl tt
            ; (i = i1) → filler a (pt B) k j r
            ; (j = i0) → inl-fill a i k i1
            ; (j = i1) → push (inl (compPath-filler
                           (merid a) (sym (merid (pt A))) (~ r) k)) i
            ; (k = i0) → sₙ i j i1
            ; (k = i1) → sₛ i j r})
       (hcomp (λ r
         → λ {(i = i0) → inl tt
             ; (i = i1) → doubleCompPath-filler
                             (push (inr (pt B)))
                             (λ i₁ → inr' (σ A a i₁ , (pt B)))
                             (sym (push (inr (pt B)))) (~ j ∧ r) k
             ; (j = i0) → inl-fill a i k r
             ; (j = i1) → push (inl (toSusp A a k)) i
             ; (k = i0) → sₙ i j r
             ; (k = i1) → sₙ i j r})
         (hcomp (λ r
           → λ {(i = i0) → inl tt
               ; (i = i1) → inl-fill₁ a i k r
               ; (j = i0) → inl-fill₁ a i k r
               ; (j = i1) → push (inl (toSusp A a k)) i
               ; (k = i0) → push (push tt (r ∧ (~ j))) i
               ; (k = i1) → push (push tt (r ∧ (~ j))) i})
       (push (inl (toSusp A a k)) i))))

    main : (y : typ B) (x : Susp (typ A))
      → Susp⋀→SuspL (SuspL→Susp⋀ (inr (x , y))) ≡ inr (x , y)
    main y north = push (inr y)
    main y south = push (inr y) ∙ λ i → inr (merid (pt A) i , y)
    main y (merid a i) j = filler a y i j i1

⋀S-base : (m : ℕ)
  → Iso (S₊∙ zero ⋀ S₊∙ m) (S₊ m)
fun (⋀S-base m) = ⋀S zero m
inv (⋀S-base m) x = inr (false , x)
rightInv (⋀S-base m) x = refl
leftInv (⋀S-base m) =
  ⋀-fun≡ _ _
    (sym (push (inl false)))
    (λ { (false , y) → refl
       ; (true , y) → sym (push (inl false)) ∙ push (inr y)})
     (λ { false i j → push (inl false) (i ∨ ~ j)
        ; true → compPath-filler (sym (push (inl false))) (push (inl true))
        ▷ cong (sym (push (inl false)) ∙_)
                (λ i → push (push tt i) )})
        λ x → compPath-filler (sym (push (inl false))) (push (inr x))

⋀S-ind : (n m : ℕ) (x : _)
  → ⋀S (suc n) m x
   ≡ Iso.inv (IsoSucSphereSusp (n + m))
      (suspFun (⋀S n m) (Iso.fun SuspSmashCommIso
        (((Iso.fun (IsoSucSphereSusp n) , IsoSucSphereSusp∙' n)
      ⋀→ idfun∙ (S₊∙ m)) x)))
⋀S-ind zero m = ⋀-fun≡ _ _
  (sym (IsoSucSphereSusp∙ m))
    (λ x → main m (fst x) (snd x))
    (mainₗ m)
    mainᵣ
  where
  F' :  (m : ℕ) → Susp ((Bool , true) ⋀ S₊∙ m) → _
  F' m = inv (IsoSucSphereSusp (zero + m)) ∘ suspFun (⋀S zero m)

  F : (m : ℕ) → Susp∙ Bool ⋀ S₊∙ m → _
  F m = F' m ∘ fun SuspSmashCommIso

  G : (m : ℕ) → _ → _
  G m = _⋀→_ {A = S₊∙ 1} {B = S₊∙ m}
         (fun (IsoSucSphereSusp zero) , (λ _ → north))
         (idfun∙ (S₊∙ m))

  main : (m : ℕ) (x : S¹) (y : S₊ m)
    → x ⌣S y
    ≡ F m (inr (S¹→SuspBool x , y))
  main m base y = sym (IsoSucSphereSusp∙ m)
  main zero (loop i) false j =
    ((cong-∙ (λ x → F zero (inr (x , false)))
             (merid false) (sym (merid true)))
    ∙ sym (rUnit loop)) (~ j) i
  main zero (loop i) true j =
    F zero (inr (rCancel (merid true) (~ j) i , false))
  main (suc m) (loop i) y j =
    cong-∙ (λ x → F (suc m) (inr (x , y)))
           (merid false) (sym (merid true)) (~ j) i
           
  mainₗ : (m : ℕ) (x : S¹)
    → PathP (λ i → IdL⌣S {m = m} x (~ i)
            ≡ F m (G m (push (inl x) i)))
             (sym (IsoSucSphereSusp∙ m))
             (main m x (ptSn m))
  mainₗ zero =
    toPropElim (λ _ → isOfHLevelPathP' 1 (isGroupoidS¹ _ _) _ _)
     (flipSquare (cong (cong (F zero)) (rUnit (push (inl north)))))
  mainₗ (suc m) x = flipSquare (help x
    ▷ (cong (cong (F (suc m))) (rUnit (push (inl (S¹→SuspBool x))))))
    where
    help : (x : S¹)
      → PathP (λ i → north ≡ main (suc m) x (ptSn (suc m)) i)
           (sym (IdL⌣S {n = 1} x))
           (cong (F (suc m)) (push (inl (S¹→SuspBool x))))
    help base = refl
    help (loop i) j k = 
      hcomp (λ r
        → λ {(i = i0) → north
            ; (i = i1) → F' (suc m)
                           (merid-fill
                            {A = Bool , true}
                            {B = S₊∙ (suc m)} true (~ r) k j)
            ; (j = i0) → rCancel-filler (merid (ptSn (suc m))) r (~ k) i
            ; (j = i1) → F (suc m)
                           (push (inl (compPath-filler
                             (merid false) (sym (merid true)) r i)) k)
            ; (k = i0) → north
            ; (k = i1) → cong-∙∙-filler
                            (λ x₁ → F (suc m) (inr (x₁ , ptSn (suc m))))
                            refl (merid false) (sym (merid true)) r (~ j) i})
       (F' (suc m) (merid-fill {A = Bool , true} {B = S₊∙ (suc m)} false k i j))
  mainᵣ : (x : S₊ m)
    → PathP (λ i → ptSn (suc m) ≡ F m (G m (push (inr x) i)))
             (sym (IsoSucSphereSusp∙ m))
             (sym (IsoSucSphereSusp∙ m))
  mainᵣ x = flipSquare ((λ i j → (IsoSucSphereSusp∙ m) (~ i))
                       ▷ cong (cong (F m)) (rUnit (push (inr x))))

⋀S-ind (suc n) m = ⋀-fun≡ _ _ refl
  (λ x → h (fst x) (snd x))
  hₗ 
  λ x → flipSquare (cong (cong (suspFun (⋀S (suc n) m)
                              ∘ fun SuspSmashCommIso))
                    (rUnit (push (inr x))))
  where
  h : (x : S₊ (suc (suc n))) (y : S₊ m)
    → (x ⌣S y)
    ≡ suspFun (⋀S (suc n) m)
       (SuspL→Susp⋀ (inr (idfun (Susp (S₊ (suc n))) x , y)))
  h north y = refl
  h south y = merid (ptSn _)
  h (merid a i) y j = compPath-filler
           (merid (a ⌣S y)) (sym (merid (ptSn (suc (n + m))))) (~ j) i

  hₗ-lem : (x : Susp (S₊ (suc n)))
    → PathP (λ i → north ≡ h x (ptSn m) i)
             (sym (IdL⌣S x))
             (cong (suspFun (⋀S (suc n) m)
                  ∘ fun SuspSmashCommIso)
                   (push (inl x)))
  hₗ-lem north = refl
  hₗ-lem south i j = merid (ptSn (suc (n + m))) (i ∧ j)
  hₗ-lem (merid a i) j k = help j k i
    where
    help : Cube (sym (cong (toSusp (S₊∙ (suc (n + m))))
                  (IdL⌣S {n = suc n} {m = m} a)
                 ∙ rCancel (merid (ptSn (suc n + m)))))
                (λ k i → suspFun (⋀S (suc n) m)
                           (SuspL→Susp⋀ (push (inl (merid a i)) k)))
                (λ j i → north)
                (λ j i → compPath-filler
                           (merid (a ⌣S ptSn m))
                           (sym (merid (ptSn (suc (n + m))))) (~ j) i)
                (λ j k → north)
                λ j k → merid (ptSn (suc (n + m))) (j ∧ k)
    help j k i =
      hcomp (λ r
        → λ {(i = i0) → north
            ; (i = i1) → merid (ptSn (suc (n + m))) (j ∧ k)
            ; (j = i0) → compPath-filler'
                           (cong (toSusp (S₊∙ (suc (n + m))))
                            (IdL⌣S {n = suc n} {m = m} a))
                           (rCancel (merid (ptSn (suc n + m)))) r (~ k) i
            ; (j = i1) → suspFun (⋀S (suc n) m)
                           (merid-fill a k i r)
            ; (k = i0) → north
            ; (k = i1) → compPath-filler
                           (merid (IdL⌣S a (~ r)))
                           (sym (merid (ptSn (suc (n + m))))) (~ j) i})
         (hcomp (λ r → λ {(i = i0) → north
                        ; (i = i1) → merid (ptSn (suc (n + m))) ((j ∨ ~ r) ∧ k)
                        ; (j = i0) → rCancel-filler (merid (ptSn _)) r (~ k) i
                        ; (j = i1) → merid (ptSn (suc (n + m))) (i ∧ k)
                        ; (k = i0) → north
                        ; (k = i1) → compPath-filler
                                       (merid (ptSn _))
                                       (sym (merid (ptSn (suc (n + m)))))
                                       (~ j ∧ r) i})
                  (merid (ptSn (suc (n + m))) (i ∧ k)))

  hₗ : (x : Susp (S₊ (suc n)))
    → PathP (λ i → IdL⌣S x (~ i)
      ≡ inv (IsoSucSphereSusp (suc n + m))
         (suspFun (⋀S (suc n) m)
          (fun SuspSmashCommIso
           (((fun (IsoSucSphereSusp (suc n)) , IsoSucSphereSusp∙' (suc n)) ⋀→
             idfun∙ (S₊∙ m))
            (push (inl x) i))))) refl (h x (ptSn m))
  hₗ x =
    flipSquare
       ((hₗ-lem x
      ▷ sym (cong (cong (inv (IsoSucSphereSusp (suc n + m))
                  ∘ suspFun (⋀S (suc n) m)
                  ∘ fun SuspSmashCommIso))
                  (sym (rUnit (push (inl x)))))))


isEquiv-⋀S : (n m : ℕ) → isEquiv (⋀S n m)
isEquiv-⋀S zero m = isoToIsEquiv (⋀S-base m)
isEquiv-⋀S (suc n) m =
  subst isEquiv (sym (funExt (⋀S-ind n m)))
    (snd (helpEq (isEquiv-⋀S n m)))
  where
  r = isoToEquiv (IsoSucSphereSusp n)

  helpEq : isEquiv (⋀S n m) → (S₊∙ (suc n) ⋀ S₊∙ m) ≃ S₊ (suc n + m)
  helpEq iseq =
    compEquiv
     (compEquiv
       (compEquiv
         (⋀≃ (r , IsoSucSphereSusp∙' n) (idEquiv (S₊ m) , refl))
         (isoToEquiv SuspSmashCommIso))
       (isoToEquiv
         (congSuspIso (equivToIso (⋀S n m , iseq)))))
      (isoToEquiv (invIso (IsoSucSphereSusp (n + m))))

SphereSmashIso : (n m : ℕ) → Iso (S₊∙ n ⋀ S₊∙ m) (S₊ (n + m))
SphereSmashIso n m = equivToIso (⋀S n m , isEquiv-⋀S n m)


module _ {ℓ ℓ' : Level} (A B : Pointed ℓ) (C : Pointed ℓ') where

  Susp∧→ : (f g : Susp∙ (A ⋀ B) →∙ C)
         → ((x : Susp (fst A × fst B)) → fst f (suspFun inr x) ≡ fst g (suspFun inr x))
         → f ≡ g
  Susp∧→ f g ind =
    ΣPathP ((funExt (λ { north → snd f ∙∙ refl ∙∙ sym (snd g)
                       ; south → cong (fst f) (sym (merid (inl tt)))
                               ∙∙ (snd f ∙∙ refl ∙∙ sym (snd g))
                               ∙∙ cong (fst g) (merid (inl tt))
                       ; (merid a i) → {!ind north -- -- cong ind (merid (a)) !}}))
                       , λ i j → doubleCompPath-filler (snd f) refl (sym (snd g)) (~ j) i)
    where
    help : Iso.inv (ΩSuspAdjointIso {A = A ⋀∙ B}) f ≡ Iso.inv ΩSuspAdjointIso g
    help = →∙Homogeneous≡ (isHomogeneousPath _ _)
              (⋀→Homogeneous≡ (isHomogeneousPath _ _)
                λ x y i j
                  → hcomp (λ k → λ {(i = i0) → {!!}
                                   ; (i = i1) → {!cong ind (merid (x , y))!}
                                   ; (j = i0) → {!doubleComp!}
                                   ; (j = i1) → {!!}})
                    {!j = i0 ⊢ snd C
j = i1 ⊢ snd C
i = i0 ⊢ ((λ i₁ → snd f (~ i₁)) ∙∙
          (λ i₁ → fst f (σ (A ⋀∙ B) (inr (x , y)) i₁)) ∙∙ snd f)
         j
i = i1 ⊢ ((λ i₁ → snd g (~ i₁)) ∙∙
          (λ i₁ →
             fst g (σ (Pushout (λ _ → tt) i∧ , snd (A ⋀∙ B)) (inr (x , y)) i₁))
          ∙∙ snd g)
         j!})

    dd = ⋀→Homogeneous≡

  SuspL→ : ∀ {ℓ ℓ' ℓ''} {A : Pointed ℓ} {B : Pointed ℓ'} {C : Pointed ℓ''}
    → (f g : Susp∙ (typ A) ⋀∙ B →∙ C)
    → ((x : Susp (typ A)) (y : fst B) → f .fst (inr (x , y)) ≡ g .fst (inr (x , y)))
    → (x : _) → fst f x ≡ fst g x
  SuspL→ f g ind (inl x) = snd f ∙ sym (snd g)
  SuspL→ f g ind (inr x) = ind (fst x) (snd x)
  SuspL→ f g ind (push (inl x) i) = {!!}
  SuspL→ f g ind (push (inr x) i) = {!!}
  SuspL→ f g ind (push (push a i₁) i) = {!!}



-- {-

-- -- -S^-expl
-- ⋀S-comm* : {n m : ℕ} (x : S₊∙ n ⋀ S₊∙ m) (p : _) (q : _)
--   → ⋀S n m x
--    ≡ subst S₊ (+-comm m n) (-S^-expl m n
--               p q
--               (⋀S m n (⋀comm→ x)))
-- ⋀S-comm* {n = n} {m} (inl x) p q = {!!}
-- ⋀S-comm* {n = n} {m} (inr (x , y)) p q = {!⌣S-comm x y!}
-- ⋀S-comm* {n = n} {m} (push a i) p q = {!!}

-- ⋀S-comm : {n m : ℕ} (x : S₊∙ n ⋀ S₊∙ m)
--   → ⋀S n m x ≡ subst S₊ (+-comm m n) (-S^ (m · n) (⋀S m n (⋀comm→ x))) 
-- ⋀S-comm {n = zero} {m = zero} (inl x) = refl
-- ⋀S-comm {n = zero} {m = suc m} (inl x) = {!!}
-- ⋀S-comm {n = suc n} {m = m} (inl x) = {!!}
-- ⋀S-comm (inr (x , y)) = ⌣S-comm x y
-- ⋀S-comm (push a i) = {!⌣S!}
-- -}



-- module _ {ℓ ℓ' : Level} {A : Pointed ℓ} {B : Pointed ℓ'} where

--  sm-fillᵣ : ∀ {ℓ} {A : Type ℓ} {x* : A} (y* : A) (p* : x* ≡ y*)
--    (y : A) → (p : x* ≡ y)
--      → sym p* ≡ (sym p* ∙∙ p ∙∙ sym p)
--  sm-fillᵣ y* p* y p j i =
--    hcomp (λ r → λ {(i = i0) → p* r
--                   ; (i = i1) → p (~ r ∧ j)
--                   ; (j = i0) → p* (~ i ∧ r)
--                   ; (j = i1) → doubleCompPath-filler
--                                  (sym p*) p (sym p) r i})
--      (p (i ∧ j))

--  sm-fillₗ : ∀ {ℓ} {A : Type ℓ} {x* : A} (y* : A) (p* : x* ≡ y*)
--       (y : A) (p : x* ≡ y)
--    → p* ≡ (p ∙∙ sym p ∙∙ p*)
--  sm-fillₗ y* p* y p j i =
--      hcomp (λ r → λ {(i = i0) → p (~ r ∧ j)
--                     ; (i = i1) → p* r
--                     ; (j = i0) → p* (r ∧ i)
--                     ; (j = i1) → doubleCompPath-filler
--                                    p (sym p) p* r i})
--        (p (~ i ∧ j))

--  sm-fillₗᵣ≡ : ∀ {ℓ} {A : Type ℓ} {x* : A} (y* : A) (p* : x* ≡ y*)
--    → sm-fillₗ _ (sym p*) _ (sym p*) ≡ sm-fillᵣ _ p* _ p*
--  sm-fillₗᵣ≡ = J> refl

--  SuspSmash→Join : Susp (A ⋀ B) → (join (typ A) (typ B))
--  SuspSmash→Join north = inr (pt B)
--  SuspSmash→Join south = inl (pt A)
--  SuspSmash→Join (merid (inl x) i) =
--    push (pt A) (pt B) (~ i)
--  SuspSmash→Join (merid (inr (x , b)) i) =
--    (sym (push x (pt B)) ∙∙ push x b ∙∙ sym (push (pt A) b)) i
--  SuspSmash→Join (merid (push (inl x) j) i) =
--    sm-fillₗ {A = join (typ A) (typ B)} _
--      (sym (push (pt A) (pt B))) _ (sym (push x (pt B))) j i
--  SuspSmash→Join (merid (push (inr x) j) i) =
--    sm-fillᵣ {A = join (typ A) (typ B)} _
--      (push (pt A) (pt B)) _  (push (pt A) x) j i
--  SuspSmash→Join (merid (push (push a k) j) i) =
--    sm-fillₗᵣ≡ _ (push (pt A) (pt B)) k j i

--  Join→SuspSmash : join (typ A) (typ B) → Susp (A ⋀ B)
--  Join→SuspSmash (inl x) = north
--  Join→SuspSmash (inr x) = south
--  Join→SuspSmash (push a b i) = merid (inr (a , b)) i

--  Join→SuspSmash→Join : (x : join (typ A) (typ B))
--    → SuspSmash→Join (Join→SuspSmash x) ≡ x
--  Join→SuspSmash→Join (inl x) = sym (push x (pt B))
--  Join→SuspSmash→Join (inr x) = push (pt A) x
--  Join→SuspSmash→Join (push a b i) j =
--    doubleCompPath-filler
--      (sym (push a (pt B))) (push a b) (sym (push (pt A) b)) (~ j) i

--  SuspSmash→Join→SuspSmash : (x : Susp (A ⋀ B))
--    → Join→SuspSmash (SuspSmash→Join x) ≡ x
--  SuspSmash→Join→SuspSmash north = sym (merid (inr (pt A , pt B)))
--  SuspSmash→Join→SuspSmash south = merid (inr (pt A , pt B))
--  SuspSmash→Join→SuspSmash (merid a i) j =
--    hcomp (λ r
--      → λ {(i = i0) → merid (inr (pt A , pt B)) (~ j ∨ ~ r)
--          ; (i = i1) → merid (inr (pt A , pt B)) (j ∧ r)
--          ; (j = i0) → Join→SuspSmash (SuspSmash→Join (merid a i))
--          ; (j = i1) → doubleCompPath-filler
--                         (sym (merid (inr (pt A , pt B))))
--                         (merid a)
--                         (sym (merid (inr (pt A , pt B)))) (~ r) i})
--        (f₁₂ j .fst a i)
--    where
--    f₁ f₂ : A ⋀∙ B →∙ (Path (Susp (A ⋀ B)) south north
--                      , sym (merid (inr (snd A , snd B))))
--    (fst f₁) a i = Join→SuspSmash (SuspSmash→Join (merid a i))
--    snd f₁ = refl
--    (fst f₂) a =
--         sym (merid (inr (pt A , pt B)))
--      ∙∙ merid a
--      ∙∙ sym (merid (inr (pt A , pt B)))
--    snd f₂ = cong₂ (λ x y → sym x ∙∙ y ∙∙ sym x)
--              refl (cong merid (push (inl (pt A))))
--           ∙ doubleCompPath≡compPath
--              (sym (merid (inr (pt A , pt B)))) _ _
--           ∙ cong₂ _∙_ refl (rCancel (merid (inr (pt A , pt B))))
--           ∙ sym (rUnit _)

--    f₁₂ : f₁ ≡ f₂
--    f₁₂ = ⋀→∙Homogeneous≡ (isHomogeneousPath _ _)
--      λ x y → cong-∙∙ Join→SuspSmash
--                     (sym (push x (pt B)))
--                     (push x y)
--                     (sym (push (pt A) y))
--            ∙ (λ i → sym (merid ((sym (push (inl x))
--                                ∙ push (inl (pt A))) i))
--                   ∙∙ merid (inr (x , y))
--                   ∙∙ sym (merid ((sym (push (inr y))
--                                ∙ push (inl (pt A))) i)))

--  SmashJoinIso : Iso (Susp (A ⋀ B)) (join (typ A) (typ B))
--  fun SmashJoinIso = SuspSmash→Join
--  inv SmashJoinIso = Join→SuspSmash
--  rightInv SmashJoinIso = Join→SuspSmash→Join
--  leftInv SmashJoinIso = SuspSmash→Join→SuspSmash

-- join→Sphere : (n m : ℕ)
--   → join (S₊ n) (S₊ m) → S₊ (suc (n + m))
-- join→Sphere n m (inl x) = ptSn _
-- join→Sphere n m (inr x) = ptSn _
-- join→Sphere n m (push a b i) = σS (a ⌣S b) i

-- joinSphereIso' : (n m : ℕ)
--   → Iso (join (S₊ n) (S₊ m)) (S₊ (suc (n + m)))
-- joinSphereIso' n m =
--   compIso (invIso (SmashJoinIso {A = S₊∙ n} {B = S₊∙ m}))
--    (compIso (congSuspIso (SphereSmashIso n m))
--     (invIso (IsoSucSphereSusp (n + m))))

-- join→Sphere≡ : (n m : ℕ) (x : _)
--   → join→Sphere n m x ≡ joinSphereIso' n m .Iso.fun x
-- join→Sphere≡ zero zero (inl x) = refl
-- join→Sphere≡ zero (suc m) (inl x) = refl
-- join→Sphere≡ (suc n) m (inl x) = refl
-- join→Sphere≡ zero zero (inr x) = refl
-- join→Sphere≡ zero (suc m) (inr x) = merid (ptSn (suc m))
-- join→Sphere≡ (suc n) zero (inr x) = merid (ptSn (suc n + zero))
-- join→Sphere≡ (suc n) (suc m) (inr x) = merid (ptSn (suc n + suc m))
-- join→Sphere≡ zero zero (push false false i) j = loop i
-- join→Sphere≡ zero zero (push false true i) j = base
-- join→Sphere≡ zero zero (push true b i) j = base
-- join→Sphere≡ zero (suc m) (push a b i) j =
--   compPath-filler
--     (merid (a ⌣S b)) (sym (merid (ptSn (suc m)))) (~ j) i
-- join→Sphere≡ (suc n) zero (push a b i) j =
--   compPath-filler
--     (merid (a ⌣S b)) (sym (merid (ptSn (suc n + zero)))) (~ j) i
-- join→Sphere≡ (suc n) (suc m) (push a b i) j =
--   compPath-filler
--     (merid (a ⌣S b)) (sym (merid (ptSn (suc n + suc m)))) (~ j) i

-- joinSphereIso : (n m : ℕ)
--   → Iso (join (S₊ n) (S₊ m)) (S₊ (suc (n + m)))
-- fun (joinSphereIso n m) = join→Sphere n m
-- inv (joinSphereIso n m) = joinSphereIso' n m .Iso.inv
-- rightInv (joinSphereIso n m) x =
--   join→Sphere≡ n m (joinSphereIso' n m .Iso.inv x)
--   ∙ joinSphereIso' n m .Iso.rightInv x
-- leftInv (joinSphereIso n m) x =
--   cong (joinSphereIso' n m .inv) (join→Sphere≡ n m x)
--   ∙ joinSphereIso' n m .Iso.leftInv x


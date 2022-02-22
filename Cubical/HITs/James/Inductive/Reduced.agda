{-

This file contains:


-}
{-# OPTIONS --safe #-}
module Cubical.HITs.James.Inductive.Reduced where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Univalence

open import Cubical.Data.Nat
open import Cubical.HITs.James.Inductive.Base
  renaming (𝕁ames to 𝕁amesConstruction ; 𝕁ames∞ to 𝕁ames∞Construction)

private
  variable
    ℓ : Level

module _
  ((X , x₀) : Pointed ℓ) where

  infixr 5 _∷_

  -- Some alternative constructions of James

  data 𝕁Red : Type ℓ where
    [] : 𝕁Red
    _∷_  : X → 𝕁Red → 𝕁Red
    unit : (x : X)(xs : 𝕁Red) → x₀ ∷ x ∷ xs ≡ x ∷ x₀ ∷ xs
    coh  : (xs : 𝕁Red) → refl ≡ unit x₀ xs

  data 𝕁 : Type ℓ where
    [] : 𝕁
    _∷_   : X → 𝕁 → 𝕁
    incl  : 𝕁 → 𝕁
    incl∷ : (x : X)(xs : 𝕁) → incl (x ∷ xs) ≡ x ∷ incl xs
    unit  : (xs : 𝕁) → incl xs ≡ x₀ ∷ xs
    coh   : (xs : 𝕁) →
      PathP (λ i → incl (incl xs) ≡ incl∷ x₀ xs i) (λ i → incl (unit xs i)) (unit (incl xs))

  data 𝕁Alt : Type ℓ where
    [] : 𝕁Alt
    _∷_   : X → 𝕁Alt → 𝕁Alt
    incl  : 𝕁Alt → 𝕁Alt
    incl∷ : (x : X)(xs : 𝕁Alt) → x₀ ∷ x ∷ xs ≡ x ∷ x₀ ∷ xs
    unit  : (xs : 𝕁Alt) → incl xs ≡ x₀ ∷ xs
    coh   : (xs : 𝕁Alt) → refl ≡ incl∷ x₀ xs


  -- The equivalence 𝕁Alt ≃ 𝕁Red

  𝕁Alt→𝕁Red : 𝕁Alt → 𝕁Red
  𝕁Alt→𝕁Red [] = []
  𝕁Alt→𝕁Red (x ∷ xs) = x ∷ 𝕁Alt→𝕁Red xs
  𝕁Alt→𝕁Red (incl xs) = x₀ ∷ 𝕁Alt→𝕁Red xs
  𝕁Alt→𝕁Red (incl∷ x xs i) = unit x (𝕁Alt→𝕁Red xs) i
  𝕁Alt→𝕁Red (unit xs i) = x₀ ∷ 𝕁Alt→𝕁Red xs
  𝕁Alt→𝕁Red (coh xs i j) = coh (𝕁Alt→𝕁Red xs) i j

  𝕁Red→𝕁Alt : 𝕁Red → 𝕁Alt
  𝕁Red→𝕁Alt [] = []
  𝕁Red→𝕁Alt (x ∷ xs) = x ∷ 𝕁Red→𝕁Alt xs
  𝕁Red→𝕁Alt (unit x xs i) = incl∷ x (𝕁Red→𝕁Alt xs) i
  𝕁Red→𝕁Alt (coh xs i j) = coh (𝕁Red→𝕁Alt xs) i j

  𝕁Red→𝕁Alt→𝕁Red : (xs : 𝕁Red) → 𝕁Alt→𝕁Red (𝕁Red→𝕁Alt xs) ≡ xs
  𝕁Red→𝕁Alt→𝕁Red [] = refl
  𝕁Red→𝕁Alt→𝕁Red (x ∷ xs) t = x ∷ 𝕁Red→𝕁Alt→𝕁Red xs t
  𝕁Red→𝕁Alt→𝕁Red (unit x xs i) t = unit x (𝕁Red→𝕁Alt→𝕁Red xs t) i
  𝕁Red→𝕁Alt→𝕁Red (coh xs i j) t = coh (𝕁Red→𝕁Alt→𝕁Red xs t) i j

  𝕁Alt→𝕁Red→𝕁Alt : (xs : 𝕁Alt) → 𝕁Red→𝕁Alt (𝕁Alt→𝕁Red xs) ≡ xs
  𝕁Alt→𝕁Red→𝕁Alt [] = refl
  𝕁Alt→𝕁Red→𝕁Alt (x ∷ xs) t = x ∷ 𝕁Alt→𝕁Red→𝕁Alt xs t
  𝕁Alt→𝕁Red→𝕁Alt (incl xs) = (λ t → x₀ ∷ 𝕁Alt→𝕁Red→𝕁Alt xs t) ∙ sym (unit xs)
  𝕁Alt→𝕁Red→𝕁Alt (incl∷ x xs i) t = incl∷ x (𝕁Alt→𝕁Red→𝕁Alt xs t) i
  𝕁Alt→𝕁Red→𝕁Alt (unit xs i) j =
    hcomp (λ k → λ
      { (i = i0) → compPath-filler (λ t → x₀ ∷ 𝕁Alt→𝕁Red→𝕁Alt xs t) (sym (unit xs)) k j
      ; (i = i1) → x₀ ∷ 𝕁Alt→𝕁Red→𝕁Alt xs j
      ; (j = i0) → x₀ ∷ 𝕁Red→𝕁Alt (𝕁Alt→𝕁Red xs)
      ; (j = i1) → unit xs (i ∨ ~ k)})
    (x₀ ∷ 𝕁Alt→𝕁Red→𝕁Alt xs j)
  𝕁Alt→𝕁Red→𝕁Alt (coh xs i j) t = coh (𝕁Alt→𝕁Red→𝕁Alt xs t) i j

  𝕁Alt≃𝕁Red : 𝕁Alt ≃ 𝕁Red
  𝕁Alt≃𝕁Red = isoToEquiv (iso 𝕁Alt→𝕁Red 𝕁Red→𝕁Alt 𝕁Red→𝕁Alt→𝕁Red 𝕁Alt→𝕁Red→𝕁Alt)

  -- The equivalence 𝕁 ≃ 𝕁Alt

  unitPath : Path (𝕁 → 𝕁) incl (x₀ ∷_)
  unitPath i xs = unit xs i

  incl∷'-filler : (x : X)(xs : 𝕁) → (i : I) → unitPath i (x ∷ xs) ≡ x ∷ unitPath i xs
  incl∷'-filler x xs i = transport-filler (λ i → unitPath i (x ∷ xs) ≡ x ∷ unitPath i xs) (incl∷ x xs) i

  incl∷' : (x : X)(xs : 𝕁) → x₀ ∷ x ∷ xs ≡ x ∷ x₀ ∷ xs
  incl∷' x xs = incl∷'-filler x xs i1

  coh'-filler : (xs : 𝕁) → (t : I) →
    PathP (λ i → unitPath t (unitPath t xs) ≡ incl∷'-filler x₀ xs t i)
          (λ i → unitPath t (unit xs (t ∨ i))) (λ i → unit (unitPath t xs) (t ∨ i))
  coh'-filler xs k =
    transport-filler (λ t →
      PathP (λ i → unitPath t (unitPath t xs) ≡ incl∷'-filler x₀ xs t i)
        (λ i → unitPath t (unit xs (t ∨ i))) (λ i → unit (unitPath t xs) (t ∨ i)))
      (coh xs) k

  coh' : (xs : 𝕁) → refl ≡ incl∷' x₀ xs
  coh' xs i j = coh'-filler xs i1 j i

  unitPathAlt : Path (𝕁Alt → 𝕁Alt) incl (x₀ ∷_)
  unitPathAlt i xs = unit xs i

  incl∷'Alt-filler : (x : X)(xs : 𝕁Alt) → (i : I) → unitPathAlt i (x ∷ xs) ≡ x ∷ unitPathAlt i xs
  incl∷'Alt-filler x xs i =
    transport-filler (λ i → unitPathAlt (~ i) (x ∷ xs) ≡ x ∷ unitPathAlt (~ i) xs) (incl∷ x xs) (~ i)

  incl∷'Alt : (x : X)(xs : 𝕁Alt) → incl (x ∷ xs) ≡ x ∷ incl xs
  incl∷'Alt x xs = incl∷'Alt-filler x xs i0

  coh'Alt-filler : (xs : 𝕁Alt) → (t : I)
    → PathP (λ i → unitPathAlt t (unitPathAlt t xs) ≡ incl∷'Alt-filler x₀ xs t i)
            (λ i → unitPathAlt t (unit xs (t ∨ i))) (λ i → unit (unitPathAlt t xs) (t ∨ i))
  coh'Alt-filler xs k =
    transport-filler (sym (λ t →
      PathP (λ i → unitPathAlt t (unitPathAlt t xs) ≡ incl∷'Alt-filler x₀ xs t i)
        (λ i → unitPathAlt t (unit xs (t ∨ i))) (λ i → unit (unitPathAlt t xs) (t ∨ i))))
      (λ i j → coh xs j i) (~ k)

  coh'Alt : (xs : 𝕁Alt)
    → PathP (λ i → incl (incl xs) ≡ incl∷'Alt x₀ xs i) (λ i → incl (unit xs i)) (unit (incl xs))
  coh'Alt xs = coh'Alt-filler xs i0

  𝕁→𝕁Alt : 𝕁 → 𝕁Alt
  𝕁→𝕁Alt [] = []
  𝕁→𝕁Alt (x ∷ xs) = x ∷ 𝕁→𝕁Alt xs
  𝕁→𝕁Alt (incl xs) = incl (𝕁→𝕁Alt xs)
  𝕁→𝕁Alt (unit xs i) = unit (𝕁→𝕁Alt xs) i
  𝕁→𝕁Alt (incl∷ x xs i) = incl∷'Alt x (𝕁→𝕁Alt xs) i
  𝕁→𝕁Alt (coh xs i j) = coh'Alt (𝕁→𝕁Alt xs) i j

  𝕁Alt→𝕁 : 𝕁Alt → 𝕁
  𝕁Alt→𝕁 [] = []
  𝕁Alt→𝕁 (x ∷ xs) = x ∷ 𝕁Alt→𝕁 xs
  𝕁Alt→𝕁 (incl xs) = incl (𝕁Alt→𝕁 xs)
  𝕁Alt→𝕁 (unit xs i) = unit (𝕁Alt→𝕁 xs) i
  𝕁Alt→𝕁 (incl∷ x xs i) = incl∷' x (𝕁Alt→𝕁 xs) i
  𝕁Alt→𝕁 (coh xs i j) = coh' (𝕁Alt→𝕁 xs) i j

  𝕁→𝕁Alt-incl∷'-filler : (x : X)(xs : 𝕁) → (i : I) → cong 𝕁→𝕁Alt (incl∷'-filler x xs i) ≡ incl∷'Alt-filler x (𝕁→𝕁Alt xs) i
  𝕁→𝕁Alt-incl∷'-filler x xs k i j =
    hfill (λ l → λ
      { (i = i0) → 𝕁→𝕁Alt (incl∷'-filler x xs l j)
      ; (i = i1) → incl∷'Alt-filler x (𝕁→𝕁Alt xs) l j
      ; (j = i0) → unit (x ∷ 𝕁→𝕁Alt xs) l
      ; (j = i1) → x ∷ unit (𝕁→𝕁Alt xs) l })
    (inS (incl∷'Alt x (𝕁→𝕁Alt xs) j)) k

  𝕁Alt→𝕁-incl∷'-filler : (x : X)(xs : 𝕁Alt)
    → (i : I) → cong 𝕁Alt→𝕁 (incl∷'Alt-filler x xs i) ≡ incl∷'-filler x (𝕁Alt→𝕁 xs) i
  𝕁Alt→𝕁-incl∷'-filler x xs k i j =
    hfill (λ l → λ
      { (i = i0) → 𝕁Alt→𝕁 (incl∷'Alt-filler x xs (~ l) j)
      ; (i = i1) → incl∷'-filler x (𝕁Alt→𝕁 xs) (~ l) j
      ; (j = i0) → unit (x ∷ 𝕁Alt→𝕁 xs) (~ l)
      ; (j = i1) → x ∷ unit (𝕁Alt→𝕁 xs) (~ l) })
    (inS (incl∷' x (𝕁Alt→𝕁 xs) j)) (~ k)

  𝕁→𝕁Alt-coh : (xs : 𝕁)
    → SquareP (λ i j → 𝕁→𝕁Alt (coh' xs i j) ≡ coh (𝕁→𝕁Alt xs) i j)
       (λ i j → x₀ ∷ x₀ ∷ 𝕁→𝕁Alt xs) (λ i j → 𝕁→𝕁Alt-incl∷'-filler x₀ xs i1 j i)
       (λ i j → x₀ ∷ x₀ ∷ 𝕁→𝕁Alt xs) (λ i j → x₀ ∷ x₀ ∷ 𝕁→𝕁Alt xs)
  𝕁→𝕁Alt-coh xs i j k =
    hcomp (λ l → λ
      { (i = i0) → unitPathAlt l (unitPathAlt l (𝕁→𝕁Alt xs))
      ; (i = i1) → 𝕁→𝕁Alt-incl∷'-filler x₀ xs l k j
      ; (j = i0) → unitPathAlt l (unit (𝕁→𝕁Alt xs) (l ∨ i))
      ; (j = i1) → unit (unitPathAlt l (𝕁→𝕁Alt xs)) (l ∨ i)
      ; (k = i0) → 𝕁→𝕁Alt (coh'-filler xs l j i)
      ; (k = i1) → coh'Alt-filler (𝕁→𝕁Alt xs) l j i })
    (coh'Alt (𝕁→𝕁Alt xs) j i)

  𝕁Alt→𝕁-coh : (xs : 𝕁Alt)
    → SquareP (λ i j → 𝕁Alt→𝕁 (coh'Alt xs i j) ≡ coh (𝕁Alt→𝕁 xs) i j)
       (λ i j → incl (unit (𝕁Alt→𝕁 xs) i)) (λ i j → unit (incl (𝕁Alt→𝕁 xs)) i)
       (λ i j → incl (incl (𝕁Alt→𝕁 xs)))   (λ i j → 𝕁Alt→𝕁-incl∷'-filler x₀ xs i0 j i)
  𝕁Alt→𝕁-coh xs i j k =
    hcomp (λ l → λ
      { (i = i0) → unitPath (~ l) (unit (𝕁Alt→𝕁 xs) (~ l ∨ j))
      ; (i = i1) → unit (unitPath (~ l) (𝕁Alt→𝕁 xs)) (~ l ∨ j)
      ; (j = i0) → unitPath (~ l) (unitPath (~ l) (𝕁Alt→𝕁 xs))
      ; (j = i1) → 𝕁Alt→𝕁-incl∷'-filler x₀ xs (~ l) k i
      ; (k = i0) → 𝕁Alt→𝕁 (coh'Alt-filler xs (~ l) i j)
      ; (k = i1) → coh'-filler (𝕁Alt→𝕁 xs) (~ l) i j })
    (coh' (𝕁Alt→𝕁 xs) j i)

  𝕁→𝕁Alt→𝕁 : (xs : 𝕁) → 𝕁Alt→𝕁 (𝕁→𝕁Alt xs) ≡ xs
  𝕁→𝕁Alt→𝕁 [] = refl
  𝕁→𝕁Alt→𝕁 (x ∷ xs) t = x ∷ 𝕁→𝕁Alt→𝕁 xs t
  𝕁→𝕁Alt→𝕁 (incl xs) t = incl (𝕁→𝕁Alt→𝕁 xs t)
  𝕁→𝕁Alt→𝕁 (unit xs i) t = unit (𝕁→𝕁Alt→𝕁 xs t) i
  𝕁→𝕁Alt→𝕁 (incl∷ x xs i) j =
    hcomp (λ k → λ
      { (i = i0) → incl∷ x (𝕁→𝕁Alt→𝕁 xs (j ∧ k)) i0
      ; (i = i1) → incl∷ x (𝕁→𝕁Alt→𝕁 xs (j ∧ k)) i1
      ; (j = i0) → 𝕁Alt→𝕁-incl∷'-filler x (𝕁→𝕁Alt xs) i0 i0 i
      ; (j = i1) → incl∷ x (𝕁→𝕁Alt→𝕁 xs k) i })
    (𝕁Alt→𝕁-incl∷'-filler x (𝕁→𝕁Alt xs) i0 j i)
  𝕁→𝕁Alt→𝕁 (coh xs i j) k =
    hcomp (λ l → λ
      { (i = i0) → coh (𝕁→𝕁Alt→𝕁 xs (k ∧ l)) i0 j
      ; (i = i1) → coh (𝕁→𝕁Alt→𝕁 xs (k ∧ l)) i1 j
      ; (j = i0) → coh (𝕁→𝕁Alt→𝕁 xs (k ∧ l)) i i0
      ; (j = i1) → cube-helper i k l
      ; (k = i0) → 𝕁Alt→𝕁-coh (𝕁→𝕁Alt xs) i j i0
      ; (k = i1) → coh (𝕁→𝕁Alt→𝕁 xs l) i j })
    (𝕁Alt→𝕁-coh (𝕁→𝕁Alt xs) i j k)
    where
      cube-helper : (i j k : I) → 𝕁
      cube-helper i j k =
        hfill (λ k → λ
          { (i = i0) → incl∷ x₀ (𝕁→𝕁Alt→𝕁 xs (j ∧ k)) i0
          ; (i = i1) → incl∷ x₀ (𝕁→𝕁Alt→𝕁 xs (j ∧ k)) i1
          ; (j = i0) → 𝕁Alt→𝕁-incl∷'-filler x₀ (𝕁→𝕁Alt xs) i0 i0 i
          ; (j = i1) → incl∷ x₀ (𝕁→𝕁Alt→𝕁 xs k) i })
        (inS (𝕁Alt→𝕁-incl∷'-filler x₀ (𝕁→𝕁Alt xs) i0 j i)) k

  𝕁Alt→𝕁→𝕁Alt : (xs : 𝕁Alt) → 𝕁→𝕁Alt (𝕁Alt→𝕁 xs) ≡ xs
  𝕁Alt→𝕁→𝕁Alt [] = refl
  𝕁Alt→𝕁→𝕁Alt (x ∷ xs) t = x ∷ 𝕁Alt→𝕁→𝕁Alt xs t
  𝕁Alt→𝕁→𝕁Alt (incl xs) t = incl (𝕁Alt→𝕁→𝕁Alt xs t)
  𝕁Alt→𝕁→𝕁Alt (unit xs i) t = unit (𝕁Alt→𝕁→𝕁Alt xs t) i
  𝕁Alt→𝕁→𝕁Alt (incl∷ x xs i) j =
    hcomp (λ k → λ
      { (i = i0) → incl∷ x (𝕁Alt→𝕁→𝕁Alt xs (j ∧ k)) i0
      ; (i = i1) → incl∷ x (𝕁Alt→𝕁→𝕁Alt xs (j ∧ k)) i1
      ; (j = i0) → 𝕁→𝕁Alt-incl∷'-filler x (𝕁Alt→𝕁 xs) i1 i0 i
      ; (j = i1) → incl∷ x (𝕁Alt→𝕁→𝕁Alt xs k) i })
    (𝕁→𝕁Alt-incl∷'-filler x (𝕁Alt→𝕁 xs) i1 j i)
  𝕁Alt→𝕁→𝕁Alt (coh xs i j) k =
    hcomp (λ l → λ
      { (i = i0) → coh (𝕁Alt→𝕁→𝕁Alt xs (k ∧ l)) i0 j
      ; (i = i1) → cube-helper j k l
      ; (j = i0) → coh (𝕁Alt→𝕁→𝕁Alt xs (k ∧ l)) i i0
      ; (j = i1) → coh (𝕁Alt→𝕁→𝕁Alt xs (k ∧ l)) i i1
      ; (k = i0) → 𝕁→𝕁Alt-coh (𝕁Alt→𝕁 xs) i j i0
      ; (k = i1) → coh (𝕁Alt→𝕁→𝕁Alt xs l) i j })
    (𝕁→𝕁Alt-coh (𝕁Alt→𝕁 xs) i j k)
    where
      cube-helper : (i j k : I) → 𝕁Alt
      cube-helper i j k =
        hfill (λ k → λ
          { (i = i0) → incl∷ x₀ (𝕁Alt→𝕁→𝕁Alt xs (j ∧ k)) i0
          ; (i = i1) → incl∷ x₀ (𝕁Alt→𝕁→𝕁Alt xs (j ∧ k)) i1
          ; (j = i0) → 𝕁→𝕁Alt-incl∷'-filler x₀ (𝕁Alt→𝕁 xs) i1 i0 i
          ; (j = i1) → incl∷ x₀ (𝕁Alt→𝕁→𝕁Alt xs k) i })
        (inS (𝕁→𝕁Alt-incl∷'-filler x₀ (𝕁Alt→𝕁 xs) i1 j i)) k

  𝕁≃𝕁Alt : 𝕁 ≃ 𝕁Alt
  𝕁≃𝕁Alt = isoToEquiv (iso 𝕁→𝕁Alt 𝕁Alt→𝕁 𝕁Alt→𝕁→𝕁Alt 𝕁→𝕁Alt→𝕁)

  -- The equivalence of family : 𝕁 ≃ 𝕁Red

  𝕁≃𝕁Red : 𝕁 ≃ 𝕁Red
  𝕁≃𝕁Red = compEquiv 𝕁≃𝕁Alt 𝕁Alt≃𝕁Red

  -- The induced equivalence of colimits
  -- Basically everything is just about refl

  data 𝕁Red∞ : Type ℓ where
    inl : 𝕁Red → 𝕁Red∞
    push : (xs : 𝕁Red) → inl xs ≡ inl (x₀ ∷ xs)

  data 𝕁Alt∞ : Type ℓ where
    inl : 𝕁Alt → 𝕁Alt∞
    push : (xs : 𝕁Alt) → inl xs ≡ inl (x₀ ∷ xs)

  data 𝕁∞ : Type ℓ where
    inl : 𝕁 → 𝕁∞
    push : (xs : 𝕁) → inl xs ≡ inl (incl xs)

  data 𝕁Path∞ (i : I) : Type ℓ where
    inl : 𝕁 → 𝕁Path∞ i
    push : (xs : 𝕁) → inl xs ≡ inl (unit xs i)

  𝕁Path∞0→𝕁∞ : 𝕁Path∞ i0 → 𝕁∞
  𝕁Path∞0→𝕁∞ (inl xs) = inl xs
  𝕁Path∞0→𝕁∞ (push xs i) = push xs i

  𝕁∞→𝕁Path∞0 : 𝕁∞ → 𝕁Path∞ i0
  𝕁∞→𝕁Path∞0 (inl xs) = inl xs
  𝕁∞→𝕁Path∞0 (push xs i) = push xs i

  𝕁Path∞0→𝕁∞→𝕁Path∞0 : (xs : 𝕁Path∞ i0) → 𝕁∞→𝕁Path∞0 (𝕁Path∞0→𝕁∞ xs) ≡ xs
  𝕁Path∞0→𝕁∞→𝕁Path∞0 (inl xs) = refl
  𝕁Path∞0→𝕁∞→𝕁Path∞0 (push xs i) = refl

  𝕁∞→𝕁Path∞0→𝕁∞ : (xs : 𝕁∞) → 𝕁Path∞0→𝕁∞ (𝕁∞→𝕁Path∞0 xs) ≡ xs
  𝕁∞→𝕁Path∞0→𝕁∞ (inl xs) = refl
  𝕁∞→𝕁Path∞0→𝕁∞ (push xs i) = refl

  𝕁Path∞1→𝕁Alt∞ : 𝕁Path∞ i1 → 𝕁Alt∞
  𝕁Path∞1→𝕁Alt∞ (inl xs) = inl (𝕁→𝕁Alt xs)
  𝕁Path∞1→𝕁Alt∞ (push xs i) = push (𝕁→𝕁Alt xs) i

  𝕁Alt∞→𝕁Path∞1 : 𝕁Alt∞ → 𝕁Path∞ i1
  𝕁Alt∞→𝕁Path∞1 (inl xs) = inl (𝕁Alt→𝕁 xs)
  𝕁Alt∞→𝕁Path∞1 (push xs i) = push (𝕁Alt→𝕁 xs) i

  𝕁Path∞1→𝕁Alt∞→𝕁Path∞1 : (xs : 𝕁Path∞ i1) → 𝕁Alt∞→𝕁Path∞1 (𝕁Path∞1→𝕁Alt∞ xs) ≡ xs
  𝕁Path∞1→𝕁Alt∞→𝕁Path∞1 (inl xs) t = inl (𝕁→𝕁Alt→𝕁 xs t)
  𝕁Path∞1→𝕁Alt∞→𝕁Path∞1 (push xs i) t = push (𝕁→𝕁Alt→𝕁 xs t) i

  𝕁Alt∞→𝕁Path∞1→𝕁Alt∞ : (xs : 𝕁Alt∞) → 𝕁Path∞1→𝕁Alt∞ (𝕁Alt∞→𝕁Path∞1 xs) ≡ xs
  𝕁Alt∞→𝕁Path∞1→𝕁Alt∞ (inl xs) t = inl (𝕁Alt→𝕁→𝕁Alt xs t)
  𝕁Alt∞→𝕁Path∞1→𝕁Alt∞ (push xs i) t = push (𝕁Alt→𝕁→𝕁Alt xs t) i

  𝕁Red∞→𝕁Alt∞ : 𝕁Red∞ → 𝕁Alt∞
  𝕁Red∞→𝕁Alt∞ (inl xs) = inl (𝕁Red→𝕁Alt xs)
  𝕁Red∞→𝕁Alt∞ (push xs i) = push (𝕁Red→𝕁Alt xs) i

  𝕁Alt∞→𝕁Red∞ : 𝕁Alt∞ → 𝕁Red∞
  𝕁Alt∞→𝕁Red∞ (inl xs) = inl (𝕁Alt→𝕁Red xs)
  𝕁Alt∞→𝕁Red∞ (push xs i) = push (𝕁Alt→𝕁Red xs) i

  𝕁Red∞→𝕁Alt∞→𝕁Red∞ : (xs : 𝕁Red∞) → 𝕁Alt∞→𝕁Red∞ (𝕁Red∞→𝕁Alt∞ xs) ≡ xs
  𝕁Red∞→𝕁Alt∞→𝕁Red∞ (inl xs) t = inl (𝕁Red→𝕁Alt→𝕁Red xs t)
  𝕁Red∞→𝕁Alt∞→𝕁Red∞ (push xs i) t = push (𝕁Red→𝕁Alt→𝕁Red xs t) i

  𝕁Alt∞→𝕁Red∞→𝕁Alt∞ : (xs : 𝕁Alt∞) → 𝕁Red∞→𝕁Alt∞ (𝕁Alt∞→𝕁Red∞ xs) ≡ xs
  𝕁Alt∞→𝕁Red∞→𝕁Alt∞ (inl xs) t = inl (𝕁Alt→𝕁Red→𝕁Alt xs t)
  𝕁Alt∞→𝕁Red∞→𝕁Alt∞ (push xs i) t = push (𝕁Alt→𝕁Red→𝕁Alt xs t) i


  -- The equivalences between colimits

  𝕁Path∞0≃𝕁∞ : 𝕁Path∞ i0 ≃ 𝕁∞
  𝕁Path∞0≃𝕁∞ = isoToEquiv (iso 𝕁Path∞0→𝕁∞ 𝕁∞→𝕁Path∞0 𝕁∞→𝕁Path∞0→𝕁∞ 𝕁Path∞0→𝕁∞→𝕁Path∞0)

  𝕁Path∞1≃𝕁Alt∞ : 𝕁Path∞ i1 ≃ 𝕁Alt∞
  𝕁Path∞1≃𝕁Alt∞ = isoToEquiv (iso 𝕁Path∞1→𝕁Alt∞ 𝕁Alt∞→𝕁Path∞1 𝕁Alt∞→𝕁Path∞1→𝕁Alt∞ 𝕁Path∞1→𝕁Alt∞→𝕁Path∞1)

  𝕁Path∞0≃𝕁Path∞1 : 𝕁Path∞ i0 ≃ 𝕁Path∞ i1
  𝕁Path∞0≃𝕁Path∞1 = pathToEquiv (λ i → 𝕁Path∞ i)

  𝕁∞≃𝕁Alt∞ : 𝕁∞ ≃ 𝕁Alt∞
  𝕁∞≃𝕁Alt∞ = compEquiv (invEquiv 𝕁Path∞0≃𝕁∞) (compEquiv 𝕁Path∞0≃𝕁Path∞1 𝕁Path∞1≃𝕁Alt∞)

  𝕁Alt∞≃𝕁Red∞ : 𝕁Alt∞ ≃ 𝕁Red∞
  𝕁Alt∞≃𝕁Red∞ = isoToEquiv (iso 𝕁Alt∞→𝕁Red∞ 𝕁Red∞→𝕁Alt∞ 𝕁Red∞→𝕁Alt∞→𝕁Red∞ 𝕁Alt∞→𝕁Red∞→𝕁Alt∞)

  𝕁∞≃𝕁Red∞ : 𝕁∞ ≃ 𝕁Red∞
  𝕁∞≃𝕁Red∞ = compEquiv 𝕁∞≃𝕁Alt∞ 𝕁Alt∞≃𝕁Red∞


  -- The equivalence with the unreduced version

  private
    𝕁ames  = 𝕁amesConstruction  (X , x₀)
    𝕁ames∞ = 𝕁ames∞Construction (X , x₀)

  -- A variant of 𝕁 with a small modification on constructor coh

  data 𝕁' : Type ℓ where
    [] : 𝕁'
    _∷_   : X → 𝕁' → 𝕁'
    incl  : 𝕁' → 𝕁'
    incl∷ : (x : X)(xs : 𝕁') → incl (x ∷ xs) ≡ x ∷ incl xs
    unit  : (xs : 𝕁') → incl xs ≡ x₀ ∷ xs
    coh   : (xs : 𝕁') → PathP (λ i → incl (unit xs i) ≡ x₀ ∷ incl xs) (unit (incl xs)) (incl∷ x₀ xs)

  data 𝕁'∞ : Type ℓ where
    inl : 𝕁' → 𝕁'∞
    push : (xs : 𝕁') → inl xs ≡ inl (incl xs)

  -- Technical lemmas

  private
    module _
      {A : Type ℓ}{a b c : A}{p : a ≡ b}{q : a ≡ c}{r : b ≡ c} where

      rotate-filler : PathP (λ i → p i ≡ c) q r
        → (i j k : I) → A
      rotate-filler sqr i j k =
        hfill (λ k → λ
          { (i = i0) → p j
          ; (i = i1) → q (j ∨ ~ k)
          ; (j = i0) → q (i ∧ ~ k)
          ; (j = i1) → r i })
        (inS (sqr j i)) k

      rotateBack-filler : PathP (λ i → a ≡ r i) p q
        → (i j k : I) → A
      rotateBack-filler sqr i j k =
        hfill (λ k → λ
          { (i = i0) → q (j ∧ k)
          ; (i = i1) → r j
          ; (j = i0) → p i
          ; (j = i1) → q (i ∨ k) })
        (inS (sqr j i)) k

      rotate : PathP (λ i → p i ≡ c) q r → PathP (λ i → a ≡ r i) p q
      rotate sqr i j = rotate-filler sqr i j i1

      rotateBack : PathP (λ i → a ≡ r i) p q → PathP (λ i → p i ≡ c) q r
      rotateBack sqr i j = rotateBack-filler sqr i j i1

      rotateForthAndBack : (sqr : _) → rotateBack (rotate sqr) ≡ sqr
      rotateForthAndBack sqr i j k =
        hcomp (λ l → λ
          { (i = i0) → rotateBack-filler (rotate sqr) j k l
          ; (i = i1) → sqr j k
          ; (j = i0) → q ((i ∧ k) ∨ (l ∧ k))
          ; (j = i1) → r k
          ; (k = i0) → p j
          ; (k = i1) → q (i ∨ j ∨ l) })
        (rotate-filler sqr k j (~ i))

      rotateBackAndForth : (sqr : _) → rotate (rotateBack sqr) ≡ sqr
      rotateBackAndForth sqr i j k =
        hcomp (λ l → λ
          { (i = i0) → rotate-filler (rotateBack sqr) j k l
          ; (i = i1) → sqr j k
          ; (j = i0) → p k
          ; (j = i1) → q ((~ i ∨ k) ∧ (~ l ∨ k))
          ; (k = i0) → q (~ (i ∨ ~ j ∨ l))
          ; (k = i1) → r j })
        (rotateBack-filler sqr k j (~ i))

    module _
      {A B : Type ℓ}
      {a b c : A}{p : a ≡ b}{q : a ≡ c}{r : b ≡ c}
      (f : A → B) where

      rotate-cong : (sqr : PathP (λ i → p i ≡ c) q r)
        → (λ i j → f (rotate sqr i j)) ≡ rotate {r = cong f r} (λ i j → f (sqr i j))
      rotate-cong sqr i j k =
        hcomp (λ l → λ
          { (i = i0) → f (rotate-filler sqr j k l)
          ; (i = i1) → rotate-filler {r = cong f r} (λ i j → f (sqr i j)) j k l
          ; (j = i0) → f (p k)
          ; (j = i1) → f (q (k ∨ ~ l))
          ; (k = i0) → f (q (j ∧ ~ l))
          ; (k = i1) → f (r j) })
        (f (sqr k j))

      rotateBack-cong : (sqr : PathP (λ i → a ≡ r i) p q)
        → (λ i j → f (rotateBack sqr i j)) ≡ rotateBack {p = cong f p} (λ i j → f (sqr i j))
      rotateBack-cong sqr i j k =
        hcomp (λ l → λ
          { (i = i0) → f (rotateBack-filler sqr j k l)
          ; (i = i1) → rotateBack-filler {p = cong f p} (λ i j → f (sqr i j)) j k l
          ; (j = i0) → f (q (k ∧ l))
          ; (j = i1) → f (r k)
          ; (k = i0) → f (p j)
          ; (k = i1) → f (q (j ∨ l)) })
        (f (sqr k j))


  𝕁→𝕁' : 𝕁 → 𝕁'
  𝕁→𝕁' [] = []
  𝕁→𝕁' (x ∷ xs) = x ∷ 𝕁→𝕁' xs
  𝕁→𝕁' (incl xs) = incl (𝕁→𝕁' xs)
  𝕁→𝕁' (incl∷ x xs i) = incl∷ x (𝕁→𝕁' xs) i
  𝕁→𝕁' (unit xs i) = unit (𝕁→𝕁' xs) i
  𝕁→𝕁' (coh xs i j) = rotate (coh (𝕁→𝕁' xs)) i j

  𝕁'→𝕁 : 𝕁' → 𝕁
  𝕁'→𝕁 [] = []
  𝕁'→𝕁 (x ∷ xs) = x ∷ 𝕁'→𝕁 xs
  𝕁'→𝕁 (incl xs) = incl (𝕁'→𝕁 xs)
  𝕁'→𝕁 (incl∷ x xs i) = incl∷ x (𝕁'→𝕁 xs) i
  𝕁'→𝕁 (unit xs i) = unit (𝕁'→𝕁 xs) i
  𝕁'→𝕁 (coh xs i j) = rotateBack (coh (𝕁'→𝕁 xs)) i j

  𝕁→𝕁'→𝕁 : (xs : 𝕁) → 𝕁'→𝕁 (𝕁→𝕁' xs) ≡ xs
  𝕁→𝕁'→𝕁 [] = refl
  𝕁→𝕁'→𝕁 (x ∷ xs) t = x ∷ 𝕁→𝕁'→𝕁 xs t
  𝕁→𝕁'→𝕁 (incl xs) t = incl (𝕁→𝕁'→𝕁 xs t)
  𝕁→𝕁'→𝕁 (incl∷ x xs i) t = incl∷ x (𝕁→𝕁'→𝕁 xs t) i
  𝕁→𝕁'→𝕁 (unit xs i) t = unit (𝕁→𝕁'→𝕁 xs t) i
  𝕁→𝕁'→𝕁 (coh xs i j) k =
    hcomp (λ l → λ
      { (i = i0) → coh (𝕁→𝕁'→𝕁 xs (k ∧ l)) i0 j
      ; (i = i1) → coh (𝕁→𝕁'→𝕁 xs (k ∧ l)) i1 j
      ; (j = i0) → coh (𝕁→𝕁'→𝕁 xs (k ∧ l)) i i0
      ; (j = i1) → coh (𝕁→𝕁'→𝕁 xs (k ∧ l)) i i1
      ; (k = i0) → rotate-cong 𝕁'→𝕁 (coh (𝕁→𝕁' xs)) (~ l) i j
      ; (k = i1) → coh (𝕁→𝕁'→𝕁 xs l) i j })
    (rotateBackAndForth (coh (𝕁'→𝕁 (𝕁→𝕁' xs))) k i j)

  𝕁'→𝕁→𝕁' : (xs : 𝕁') → 𝕁→𝕁' (𝕁'→𝕁 xs) ≡ xs
  𝕁'→𝕁→𝕁' [] = refl
  𝕁'→𝕁→𝕁' (x ∷ xs) t = x ∷ 𝕁'→𝕁→𝕁' xs t
  𝕁'→𝕁→𝕁' (incl xs) t = incl (𝕁'→𝕁→𝕁' xs t)
  𝕁'→𝕁→𝕁' (incl∷ x xs i) t = incl∷ x (𝕁'→𝕁→𝕁' xs t) i
  𝕁'→𝕁→𝕁' (unit xs i) t = unit (𝕁'→𝕁→𝕁' xs t) i
  𝕁'→𝕁→𝕁' (coh xs i j) k =
    hcomp (λ l → λ
      { (i = i0) → coh (𝕁'→𝕁→𝕁' xs (k ∧ l)) i0 j
      ; (i = i1) → coh (𝕁'→𝕁→𝕁' xs (k ∧ l)) i1 j
      ; (j = i0) → coh (𝕁'→𝕁→𝕁' xs (k ∧ l)) i i0
      ; (j = i1) → coh (𝕁'→𝕁→𝕁' xs (k ∧ l)) i i1
      ; (k = i0) → rotateBack-cong 𝕁→𝕁' (coh (𝕁'→𝕁  xs)) (~ l) i j
      ; (k = i1) → coh (𝕁'→𝕁→𝕁' xs l) i j })
    (rotateForthAndBack (coh (𝕁→𝕁' (𝕁'→𝕁 xs))) k i j)

  𝕁∞→𝕁'∞ : 𝕁∞ → 𝕁'∞
  𝕁∞→𝕁'∞ (inl xs) = inl (𝕁→𝕁' xs)
  𝕁∞→𝕁'∞ (push xs i) = push (𝕁→𝕁' xs) i

  𝕁'∞→𝕁∞ : 𝕁'∞ → 𝕁∞
  𝕁'∞→𝕁∞ (inl xs) = inl (𝕁'→𝕁 xs)
  𝕁'∞→𝕁∞ (push xs i) = push (𝕁'→𝕁 xs) i

  𝕁∞→𝕁'∞→𝕁∞ : (xs : 𝕁∞) → 𝕁'∞→𝕁∞ (𝕁∞→𝕁'∞ xs) ≡ xs
  𝕁∞→𝕁'∞→𝕁∞ (inl xs) t = inl (𝕁→𝕁'→𝕁 xs t)
  𝕁∞→𝕁'∞→𝕁∞ (push xs i) t = push (𝕁→𝕁'→𝕁 xs t) i

  𝕁'∞→𝕁∞→𝕁'∞ : (xs : 𝕁'∞) → 𝕁∞→𝕁'∞ (𝕁'∞→𝕁∞ xs) ≡ xs
  𝕁'∞→𝕁∞→𝕁'∞ (inl xs) t = inl (𝕁'→𝕁→𝕁' xs t)
  𝕁'∞→𝕁∞→𝕁'∞ (push xs i) t = push (𝕁'→𝕁→𝕁' xs t) i

  index : 𝕁' → ℕ
  index [] = 0
  index (x ∷ xs) = 1 + index xs
  index (incl xs) = 1 + index xs
  index (incl∷ x xs i) = 2 + index xs
  index (unit xs i) = 1 + index xs
  index (coh xs i j) = 2 + index xs

  𝕁ames→𝕁' : {n : ℕ} → 𝕁ames n → 𝕁'
  𝕁ames→𝕁' [] = []
  𝕁ames→𝕁' (x ∷ xs) = x ∷ 𝕁ames→𝕁' xs
  𝕁ames→𝕁' (incl xs) = incl (𝕁ames→𝕁' xs)
  𝕁ames→𝕁' (incl∷ x xs i) = incl∷ x (𝕁ames→𝕁' xs) i
  𝕁ames→𝕁' (unit xs i) = unit (𝕁ames→𝕁' xs) i
  𝕁ames→𝕁' (coh xs i j) = coh (𝕁ames→𝕁' xs) i j

  𝕁'→𝕁ames : (xs : 𝕁') → 𝕁ames (index xs)
  𝕁'→𝕁ames [] = []
  𝕁'→𝕁ames (x ∷ xs) = x ∷ 𝕁'→𝕁ames xs
  𝕁'→𝕁ames (incl xs) = incl (𝕁'→𝕁ames xs)
  𝕁'→𝕁ames (incl∷ x xs i) = incl∷ x (𝕁'→𝕁ames xs) i
  𝕁'→𝕁ames (unit xs i) = unit (𝕁'→𝕁ames xs) i
  𝕁'→𝕁ames (coh xs i j) = coh (𝕁'→𝕁ames xs) i j

  𝕁'→𝕁ames→𝕁' : (xs : 𝕁') → 𝕁ames→𝕁' (𝕁'→𝕁ames xs) ≡ xs
  𝕁'→𝕁ames→𝕁' [] = refl
  𝕁'→𝕁ames→𝕁' (x ∷ xs) t = x ∷ 𝕁'→𝕁ames→𝕁' xs t
  𝕁'→𝕁ames→𝕁' (incl xs) t = incl (𝕁'→𝕁ames→𝕁' xs t)
  𝕁'→𝕁ames→𝕁' (incl∷ x xs i) t = incl∷ x (𝕁'→𝕁ames→𝕁' xs t) i
  𝕁'→𝕁ames→𝕁' (unit xs i) t = unit (𝕁'→𝕁ames→𝕁' xs t) i
  𝕁'→𝕁ames→𝕁' (coh xs i j) t = coh (𝕁'→𝕁ames→𝕁' xs t) i j

  index-path : {n : ℕ}(xs : 𝕁ames n) → index (𝕁ames→𝕁' xs) ≡ n
  index-path [] = refl
  index-path (x ∷ xs) t = 1 + index-path xs t
  index-path (incl xs) t = 1 + index-path xs t
  index-path (incl∷ x xs i) t = 2 + index-path xs t
  index-path (unit xs i) t = 1 + index-path xs t
  index-path (coh xs i j) t = 2 + index-path xs t

  𝕁ames→𝕁'→𝕁ames : {n : ℕ}(xs : 𝕁ames n)
    → PathP (λ i → 𝕁ames (index-path xs i)) (𝕁'→𝕁ames (𝕁ames→𝕁' xs)) xs
  𝕁ames→𝕁'→𝕁ames [] = refl
  𝕁ames→𝕁'→𝕁ames (x ∷ xs) t = x ∷ 𝕁ames→𝕁'→𝕁ames xs t
  𝕁ames→𝕁'→𝕁ames (incl xs) t = incl (𝕁ames→𝕁'→𝕁ames xs t)
  𝕁ames→𝕁'→𝕁ames (incl∷ x xs i) t = incl∷ x (𝕁ames→𝕁'→𝕁ames xs t) i
  𝕁ames→𝕁'→𝕁ames (unit xs i) t = unit (𝕁ames→𝕁'→𝕁ames xs t) i
  𝕁ames→𝕁'→𝕁ames (coh xs i j) t = coh (𝕁ames→𝕁'→𝕁ames xs t) i j

  𝕁ames∞→𝕁'∞ : 𝕁ames∞ → 𝕁'∞
  𝕁ames∞→𝕁'∞ (inl xs) = inl (𝕁ames→𝕁' xs)
  𝕁ames∞→𝕁'∞ (push xs i) = push (𝕁ames→𝕁' xs) i

  𝕁'∞→𝕁ames∞ : 𝕁'∞ → 𝕁ames∞
  𝕁'∞→𝕁ames∞ (inl xs) = inl (𝕁'→𝕁ames xs)
  𝕁'∞→𝕁ames∞ (push xs i) = push (𝕁'→𝕁ames xs) i

  𝕁ames∞→𝕁'∞→𝕁ames∞ : (xs : 𝕁ames∞) → 𝕁'∞→𝕁ames∞ (𝕁ames∞→𝕁'∞ xs) ≡ xs
  𝕁ames∞→𝕁'∞→𝕁ames∞ (inl xs) t = inl (𝕁ames→𝕁'→𝕁ames xs t)
  𝕁ames∞→𝕁'∞→𝕁ames∞ (push xs i) t = push (𝕁ames→𝕁'→𝕁ames xs t) i

  𝕁'∞→𝕁ames∞→𝕁'∞ : (xs : 𝕁'∞) → 𝕁ames∞→𝕁'∞ (𝕁'∞→𝕁ames∞ xs) ≡ xs
  𝕁'∞→𝕁ames∞→𝕁'∞ (inl xs) t = inl (𝕁'→𝕁ames→𝕁' xs t)
  𝕁'∞→𝕁ames∞→𝕁'∞ (push xs i) t = push (𝕁'→𝕁ames→𝕁' xs t) i

  -- The equivalence with the modified 𝕁'

  𝕁∞≃𝕁'∞ : 𝕁∞ ≃ 𝕁'∞
  𝕁∞≃𝕁'∞ = isoToEquiv (iso 𝕁∞→𝕁'∞ 𝕁'∞→𝕁∞ 𝕁'∞→𝕁∞→𝕁'∞ 𝕁∞→𝕁'∞→𝕁∞)

  𝕁ames∞≃𝕁'∞ : 𝕁ames∞ ≃ 𝕁'∞
  𝕁ames∞≃𝕁'∞ = isoToEquiv (iso 𝕁ames∞→𝕁'∞ 𝕁'∞→𝕁ames∞ 𝕁'∞→𝕁ames∞→𝕁'∞ 𝕁ames∞→𝕁'∞→𝕁ames∞)

  𝕁ames∞≃𝕁∞ : 𝕁ames∞ ≃ 𝕁∞
  𝕁ames∞≃𝕁∞ = compEquiv 𝕁ames∞≃𝕁'∞ (invEquiv 𝕁∞≃𝕁'∞)


  -- The main equivalence:

  𝕁ames∞≃𝕁Red∞ : 𝕁ames∞ ≃ 𝕁Red∞
  𝕁ames∞≃𝕁Red∞ = compEquiv 𝕁ames∞≃𝕁∞ 𝕁∞≃𝕁Red∞

{-

This file contains:
  - Some alternative inductive definitions of James, and they give the same results.

  The most relevant one is called `𝕁Red` because it is much simpler.
  It has fewer constructors, among which the 2-dimensional constructor `coh`
  has a form essentially more clearer, and it avoids indexes.

-}
module Cubical.HITs.James.Inductive.Reduced where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Univalence

open import Cubical.Data.Nat
open import Cubical.HITs.SequentialColimit
open import Cubical.HITs.James.Inductive.Base
  renaming (𝕁ames to 𝕁amesConstruction ; 𝕁ames∞ to 𝕁ames∞Construction)

private
  variable
    ℓ : Level

module _
  ((X , x₀) : Pointed ℓ) where

  infixr 5 _∷_

  -- Inductive James with fewer constructors

  data 𝕁Red : Type ℓ where
    [] : 𝕁Red
    _∷_  : X → 𝕁Red → 𝕁Red
    unit : (x : X)(xs : 𝕁Red) → x₀ ∷ x ∷ xs ≡ x ∷ x₀ ∷ xs
    coh  : (xs : 𝕁Red) → refl ≡ unit x₀ xs

  data 𝕁Red∞ : Type ℓ where
    incl : 𝕁Red → 𝕁Red∞
    push : (xs : 𝕁Red) → incl xs ≡ incl (x₀ ∷ xs)


  -- Auxiliary constructions
  -- The following square of types is defined as HIT over I × I.
  -- Notice that the constructor `incl∷` can be seen parametrized by i, `coh` by both i j,
  -- and other constructors are constant.

  data 𝕁Square (i j : I) : Type ℓ where
    []    : 𝕁Square i j
    _∷_   : X → 𝕁Square i j → 𝕁Square i j
    incl  : 𝕁Square i j → 𝕁Square i j
    unit  : (xs : 𝕁Square i j) → incl xs ≡ x₀ ∷ xs
    incl∷ : (x : X)(xs : 𝕁Square i j) → unit (x ∷ xs) i ≡ x ∷ unit xs i
    coh   : (xs : 𝕁Square i j) →
      PathP (λ k → unit (unit xs (i ∨ k)) i ≡ unit (unit xs i) (i ∨ j ∨ k))
            (λ k → unit (unit xs i) (i ∨ j ∧ k)) (incl∷ x₀ xs)

  -- What we need actually is its diagonal.
  𝕁Path : I → Type ℓ
  𝕁Path i = 𝕁Square i (~ i)

  -- If you expand the very definition at end points,
  -- you will find that `𝕁Red` is almost a deformation retraction of `𝕁1`,
  -- and `𝕁0` is almost the same as the original inductive definition of James.
  -- That explains why the isomorphisms given bellow are mainly of c-c, c-v and refls.
  𝕁0 = 𝕁Path i0
  𝕁1 = 𝕁Path i1

  data 𝕁Path∞ (i : I) : Type ℓ where
    incl : 𝕁Path i → 𝕁Path∞ i
    push : (xs : 𝕁Path i) → incl xs ≡ incl (unit xs i)

  𝕁0∞ = 𝕁Path∞ i0
  𝕁1∞ = 𝕁Path∞ i1


  -- The equivalence 𝕁1 ≃ 𝕁Red
  -- This part reduces the constructors.

  𝕁1→𝕁Red : 𝕁1 → 𝕁Red
  𝕁1→𝕁Red [] = []
  𝕁1→𝕁Red (x ∷ xs) = x ∷ 𝕁1→𝕁Red xs
  𝕁1→𝕁Red (incl xs) = x₀ ∷ 𝕁1→𝕁Red xs
  𝕁1→𝕁Red (incl∷ x xs i) = unit x (𝕁1→𝕁Red xs) i
  𝕁1→𝕁Red (unit xs i) = x₀ ∷ 𝕁1→𝕁Red xs
  𝕁1→𝕁Red (coh xs i j) = coh (𝕁1→𝕁Red xs) i j

  𝕁Red→𝕁1 : 𝕁Red → 𝕁1
  𝕁Red→𝕁1 [] = []
  𝕁Red→𝕁1 (x ∷ xs) = x ∷ 𝕁Red→𝕁1 xs
  𝕁Red→𝕁1 (unit x xs i) = incl∷ x (𝕁Red→𝕁1 xs) i
  𝕁Red→𝕁1 (coh xs i j) = coh (𝕁Red→𝕁1 xs) i j

  𝕁Red→𝕁1→𝕁Red : (xs : 𝕁Red) → 𝕁1→𝕁Red (𝕁Red→𝕁1 xs) ≡ xs
  𝕁Red→𝕁1→𝕁Red [] = refl
  𝕁Red→𝕁1→𝕁Red (x ∷ xs) t = x ∷ 𝕁Red→𝕁1→𝕁Red xs t
  𝕁Red→𝕁1→𝕁Red (unit x xs i) t = unit x (𝕁Red→𝕁1→𝕁Red xs t) i
  𝕁Red→𝕁1→𝕁Red (coh xs i j) t = coh (𝕁Red→𝕁1→𝕁Red xs t) i j

  𝕁1→𝕁Red→𝕁1 : (xs : 𝕁1) → 𝕁Red→𝕁1 (𝕁1→𝕁Red xs) ≡ xs
  𝕁1→𝕁Red→𝕁1 [] = refl
  𝕁1→𝕁Red→𝕁1 (x ∷ xs) t = x ∷ 𝕁1→𝕁Red→𝕁1 xs t
  𝕁1→𝕁Red→𝕁1 (incl xs) = (λ t → x₀ ∷ 𝕁1→𝕁Red→𝕁1 xs t) ∙ sym (unit xs)
  𝕁1→𝕁Red→𝕁1 (incl∷ x xs i) t = incl∷ x (𝕁1→𝕁Red→𝕁1 xs t) i
  𝕁1→𝕁Red→𝕁1 (unit xs i) j =
    hcomp (λ k → λ
      { (i = i0) → compPath-filler (λ t → x₀ ∷ 𝕁1→𝕁Red→𝕁1 xs t) (sym (unit xs)) k j
      ; (i = i1) → x₀ ∷ 𝕁1→𝕁Red→𝕁1 xs j
      ; (j = i0) → x₀ ∷ 𝕁Red→𝕁1 (𝕁1→𝕁Red xs)
      ; (j = i1) → unit xs (i ∨ ~ k)})
    (x₀ ∷ 𝕁1→𝕁Red→𝕁1 xs j)
  𝕁1→𝕁Red→𝕁1 (coh xs i j) t = coh (𝕁1→𝕁Red→𝕁1 xs t) i j

  𝕁Red∞→𝕁1∞ : 𝕁Red∞ → 𝕁1∞
  𝕁Red∞→𝕁1∞ (incl xs) = incl (𝕁Red→𝕁1 xs)
  𝕁Red∞→𝕁1∞ (push xs i) = push (𝕁Red→𝕁1 xs) i

  𝕁1∞→𝕁Red∞ : 𝕁1∞ → 𝕁Red∞
  𝕁1∞→𝕁Red∞ (incl xs) = incl (𝕁1→𝕁Red xs)
  𝕁1∞→𝕁Red∞ (push xs i) = push (𝕁1→𝕁Red xs) i

  𝕁Red∞→𝕁1∞→𝕁Red∞ : (xs : 𝕁Red∞) → 𝕁1∞→𝕁Red∞ (𝕁Red∞→𝕁1∞ xs) ≡ xs
  𝕁Red∞→𝕁1∞→𝕁Red∞ (incl xs) t = incl (𝕁Red→𝕁1→𝕁Red xs t)
  𝕁Red∞→𝕁1∞→𝕁Red∞ (push xs i) t = push (𝕁Red→𝕁1→𝕁Red xs t) i

  𝕁1∞→𝕁Red∞→𝕁1∞ : (xs : 𝕁1∞) → 𝕁Red∞→𝕁1∞ (𝕁1∞→𝕁Red∞ xs) ≡ xs
  𝕁1∞→𝕁Red∞→𝕁1∞ (incl xs) t = incl (𝕁1→𝕁Red→𝕁1 xs t)
  𝕁1∞→𝕁Red∞→𝕁1∞ (push xs i) t = push (𝕁1→𝕁Red→𝕁1 xs t) i

  𝕁1∞≃𝕁Red∞ : 𝕁1∞ ≃ 𝕁Red∞
  𝕁1∞≃𝕁Red∞ = isoToEquiv (iso 𝕁1∞→𝕁Red∞ 𝕁Red∞→𝕁1∞ 𝕁Red∞→𝕁1∞→𝕁Red∞ 𝕁1∞→𝕁Red∞→𝕁1∞)


  -- The equivalence 𝕁ames ≃ 𝕁0
  -- This part removes the indexes.

  private
    𝕁ames  = 𝕁amesConstruction  (X , x₀)
    𝕁ames∞ = 𝕁ames∞Construction (X , x₀)

  index : 𝕁0 → ℕ
  index [] = 0
  index (x ∷ xs) = 1 + index xs
  index (incl xs) = 1 + index xs
  index (incl∷ x xs i) = 2 + index xs
  index (unit xs i) = 1 + index xs
  index (coh xs i j) = 2 + index xs

  𝕁ames→𝕁0 : {n : ℕ} → 𝕁ames n → 𝕁0
  𝕁ames→𝕁0 [] = []
  𝕁ames→𝕁0 (x ∷ xs) = x ∷ 𝕁ames→𝕁0 xs
  𝕁ames→𝕁0 (incl xs) = incl (𝕁ames→𝕁0 xs)
  𝕁ames→𝕁0 (incl∷ x xs i) = incl∷ x (𝕁ames→𝕁0 xs) i
  𝕁ames→𝕁0 (unit xs i) = unit (𝕁ames→𝕁0 xs) i
  𝕁ames→𝕁0 (coh xs i j) = coh (𝕁ames→𝕁0 xs) i j

  𝕁0→𝕁ames : (xs : 𝕁0) → 𝕁ames (index xs)
  𝕁0→𝕁ames [] = []
  𝕁0→𝕁ames (x ∷ xs) = x ∷ 𝕁0→𝕁ames xs
  𝕁0→𝕁ames (incl xs) = incl (𝕁0→𝕁ames xs)
  𝕁0→𝕁ames (incl∷ x xs i) = incl∷ x (𝕁0→𝕁ames xs) i
  𝕁0→𝕁ames (unit xs i) = unit (𝕁0→𝕁ames xs) i
  𝕁0→𝕁ames (coh xs i j) = coh (𝕁0→𝕁ames xs) i j

  𝕁0→𝕁ames→𝕁0 : (xs : 𝕁0) → 𝕁ames→𝕁0 (𝕁0→𝕁ames xs) ≡ xs
  𝕁0→𝕁ames→𝕁0 [] = refl
  𝕁0→𝕁ames→𝕁0 (x ∷ xs) t = x ∷ 𝕁0→𝕁ames→𝕁0 xs t
  𝕁0→𝕁ames→𝕁0 (incl xs) t = incl (𝕁0→𝕁ames→𝕁0 xs t)
  𝕁0→𝕁ames→𝕁0 (incl∷ x xs i) t = incl∷ x (𝕁0→𝕁ames→𝕁0 xs t) i
  𝕁0→𝕁ames→𝕁0 (unit xs i) t = unit (𝕁0→𝕁ames→𝕁0 xs t) i
  𝕁0→𝕁ames→𝕁0 (coh xs i j) t = coh (𝕁0→𝕁ames→𝕁0 xs t) i j

  index-path : {n : ℕ}(xs : 𝕁ames n) → index (𝕁ames→𝕁0 xs) ≡ n
  index-path [] = refl
  index-path (x ∷ xs) t = 1 + index-path xs t
  index-path (incl xs) t = 1 + index-path xs t
  index-path (incl∷ x xs i) t = 2 + index-path xs t
  index-path (unit xs i) t = 1 + index-path xs t
  index-path (coh xs i j) t = 2 + index-path xs t

  𝕁ames→𝕁0→𝕁ames : {n : ℕ}(xs : 𝕁ames n)
    → PathP (λ i → 𝕁ames (index-path xs i)) (𝕁0→𝕁ames (𝕁ames→𝕁0 xs)) xs
  𝕁ames→𝕁0→𝕁ames [] = refl
  𝕁ames→𝕁0→𝕁ames (x ∷ xs) t = x ∷ 𝕁ames→𝕁0→𝕁ames xs t
  𝕁ames→𝕁0→𝕁ames (incl xs) t = incl (𝕁ames→𝕁0→𝕁ames xs t)
  𝕁ames→𝕁0→𝕁ames (incl∷ x xs i) t = incl∷ x (𝕁ames→𝕁0→𝕁ames xs t) i
  𝕁ames→𝕁0→𝕁ames (unit xs i) t = unit (𝕁ames→𝕁0→𝕁ames xs t) i
  𝕁ames→𝕁0→𝕁ames (coh xs i j) t = coh (𝕁ames→𝕁0→𝕁ames xs t) i j

  𝕁ames∞→𝕁0∞ : 𝕁ames∞ → 𝕁0∞
  𝕁ames∞→𝕁0∞ (incl xs)   = incl (𝕁ames→𝕁0 xs)
  𝕁ames∞→𝕁0∞ (push xs i) = push (𝕁ames→𝕁0 xs) i

  𝕁0∞→𝕁ames∞ : 𝕁0∞ → 𝕁ames∞
  𝕁0∞→𝕁ames∞ (incl xs)   = incl (𝕁0→𝕁ames xs)
  𝕁0∞→𝕁ames∞ (push xs i) = push (𝕁0→𝕁ames xs) i

  𝕁ames∞→𝕁0∞→𝕁ames∞ : (xs : 𝕁ames∞) → 𝕁0∞→𝕁ames∞ (𝕁ames∞→𝕁0∞ xs) ≡ xs
  𝕁ames∞→𝕁0∞→𝕁ames∞ (incl xs)   t = incl (𝕁ames→𝕁0→𝕁ames xs t)
  𝕁ames∞→𝕁0∞→𝕁ames∞ (push xs i) t = push (𝕁ames→𝕁0→𝕁ames xs t) i

  𝕁0∞→𝕁ames∞→𝕁0∞ : (xs : 𝕁0∞) → 𝕁ames∞→𝕁0∞ (𝕁0∞→𝕁ames∞ xs) ≡ xs
  𝕁0∞→𝕁ames∞→𝕁0∞ (incl xs)   t = incl (𝕁0→𝕁ames→𝕁0 xs t)
  𝕁0∞→𝕁ames∞→𝕁0∞ (push xs i) t = push (𝕁0→𝕁ames→𝕁0 xs t) i

  𝕁ames∞≃𝕁0∞ : 𝕁ames∞ ≃ 𝕁0∞
  𝕁ames∞≃𝕁0∞ = isoToEquiv (iso 𝕁ames∞→𝕁0∞ 𝕁0∞→𝕁ames∞ 𝕁0∞→𝕁ames∞→𝕁0∞ 𝕁ames∞→𝕁0∞→𝕁ames∞)


  -- The main equivalence:

  𝕁ames∞≃𝕁Red∞ : 𝕁ames∞ ≃ 𝕁Red∞
  𝕁ames∞≃𝕁Red∞ = compEquiv 𝕁ames∞≃𝕁0∞ (compEquiv (pathToEquiv (λ i → 𝕁Path∞ i)) 𝕁1∞≃𝕁Red∞)


  -- Test of canonicity
  private
    -- It's good for [].
    eq1 : 𝕁ames∞≃𝕁Red∞ .fst (incl []) ≡ incl []
    eq1 = refl

    -- Without regularity, "obvious" equality doesn't hold definitionally.
    eq2 : (x : X) → 𝕁ames∞≃𝕁Red∞ .fst (incl (x ∷ [])) ≡ incl (x ∷ [])
    eq2 _ = transportRefl _

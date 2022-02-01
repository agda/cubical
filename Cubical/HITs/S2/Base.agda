{-# OPTIONS --safe #-}
module Cubical.HITs.S2.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Pointed

data S² : Type₀ where
  base : S²
  surf : PathP (λ i → base ≡ base) refl refl

S²∙ : Pointed ℓ-zero
S²∙ = S² , base

S²ToSetElim : ∀ {ℓ} {A : S² → Type ℓ}
           → ((x : S²) → isSet (A x))
           → A base
           → (x : S²) → A x
S²ToSetElim set b base = b
S²ToSetElim set b (surf i j) =
  isOfHLevel→isOfHLevelDep 2 set b b {a0 = refl} {a1 = refl} refl refl surf i j

-- Wedge connectivity lemmas for S² (binary maps 2-groupoids)
wedgeconFunS² : ∀ {ℓ} {P : S² → S² → Type ℓ}
         → ((x y : _) → isOfHLevel 4 (P x y))
         → (l : ((x : S²) → P x base))
         → (r : (x : S²) → P base x)
         → l base ≡ r base
         → (x y : _) → P x y
wedgeconFunS² {P = P} hlev l r p base y = r y
wedgeconFunS² {P = P} hlev l r p (surf i i₁) y = help y i i₁
  where
  help : (y : S²) → SquareP (λ i j → P (surf i j) y)
                     (λ _ → r y) (λ _ → r y)
                     (λ _ → r y) λ _ → r y
  help =
    S²ToSetElim (λ _ → isOfHLevelPathP' 2 (isOfHLevelPathP' 3 (hlev _ _) _ _) _ _)
               λ w j → hcomp (λ k → λ { (j = i0) → p k
                                        ; (j = i1) → p k
                                        ; (w = i0) → p k
                                        ; (w = i1) → p k})
                              (l (surf w j))

wedgeconFunS²Id : ∀ {ℓ} {P : S² → S² → Type ℓ}
         → (h : ((x y : _) → isOfHLevel 4 (P x y)))
         → (l : ((x : S²) → P x base))
         → (r : (x : S²) → P base x)
         → (p : l base ≡ r base)
         → (x : S²) → wedgeconFunS² h l r p x base ≡ l x
wedgeconFunS²Id h l r p base = sym p
wedgeconFunS²Id h l r p (surf i j) k =
  hcomp (λ w → λ {(i = i0) → p (~ k ∧ w)
                 ; (i = i1) → p (~ k ∧ w)
                 ; (j = i0) → p (~ k ∧ w)
                 ; (j = i1) → p (~ k ∧ w)
                 ; (k = i1) → l (surf i j)})
        (l (surf i j))

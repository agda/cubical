{-# OPTIONS --safe #-}

module Cubical.HITs.FreeComMonoids.AssocListFunctions where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

open import Cubical.HITs.AssocList

private variable
  ℓ : Level
  A : Type ℓ

infixr 30 _++_

_++_ : (xs ys : AssocList A) → AssocList A
⟨⟩ ++ ys = ys
(⟨ a , n ⟩∷ xs) ++ ys = ⟨ a , n ⟩∷ (xs ++ ys)
per a b xs i ++ ys = per a b (xs ++ ys) i
agg a m n xs i ++ ys = agg a m n (xs ++ ys) i
del a xs i ++ ys = del a (xs ++ ys) i
trunc xs ys p q i j ++ zs =
  trunc (xs ++ zs) (ys ++ zs) (cong (_++ _) p) (cong (_++ _) q) i j

unitl-++ : (xs : AssocList A) → ⟨⟩ ++ xs ≡ xs
unitl-++ xs = refl

unitr-++ : (xs : AssocList A) → xs ++ ⟨⟩ ≡ xs
unitr-++ = ElimProp.f (trunc _ _) refl λ _ _ → cong (⟨ _ , _ ⟩∷_)

assoc-++ : (xs ys zs : AssocList A) → xs ++ (ys ++ zs) ≡ (xs ++ ys) ++ zs
assoc-++ = ElimProp.f (isPropΠ2 (λ _ _ → trunc _ _))
                      (λ ys zs → refl)
                      λ x n p ys zs → cong (⟨ _ , _ ⟩∷_) (p ys zs)

cons-++ : ∀ x n (xs : AssocList A) → ⟨ x , n ⟩∷ xs ≡ xs ++ (⟨ x , n ⟩∷ ⟨⟩)
cons-++ x n = ElimProp.f (trunc _ _) refl
  λ y m p → multiPer _ _ _ _ _ ∙ cong (⟨ _ , _ ⟩∷_) p

comm-++ : (xs ys : AssocList A) → xs ++ ys ≡ ys ++ xs
comm-++ = ElimProp.f (isPropΠ (λ _ → trunc _ _))
  (sym ∘ unitr-++)
  λ x n {xs} p ys → cong (⟨ _ , _ ⟩∷_) (p ys)
                  ∙ cong (_++ _) (cons-++ x n ys)
                  ∙ sym (assoc-++ ys _ xs)

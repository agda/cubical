{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.FiniteMultiset.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat
open import Cubical.Relation.Nullary
open import Cubical.HITs.FiniteMultiset.Base
open import Cubical.Structures.MultiSet
open import Cubical.Relation.Nullary.DecidableEq

private
  variable
    A : Type₀

infixr 30 _++_

_++_ : ∀ (xs ys : FMSet A) → FMSet A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ xs ++ ys
comm x y xs i ++ ys = comm x y (xs ++ ys) i
trunc xs zs p q i j ++ ys =
  trunc (xs ++ ys) (zs ++ ys) (cong (_++ ys) p) (cong (_++ ys) q) i j

unitl-++ : ∀ (xs : FMSet A) → [] ++ xs ≡ xs
unitl-++ xs = refl

unitr-++ : ∀ (xs : FMSet A) → xs ++ [] ≡ xs
unitr-++ = ElimProp.f (trunc _ _) refl (λ x p → cong (_∷_ x) p)

assoc-++ : ∀ (xs ys zs : FMSet A) → xs ++ (ys ++ zs) ≡ (xs ++ ys) ++ zs
assoc-++ = ElimProp.f (isPropΠ2 (λ _ _ → trunc _ _))
                      (λ ys zs → refl)
                      (λ x p ys zs → cong (_∷_ x) (p ys zs))

cons-++ : ∀ (x : A) (xs : FMSet A) → x ∷ xs ≡ xs ++ [ x ]
cons-++ x = ElimProp.f (trunc _ _)
  refl
  (λ y {xs} p → comm x y xs ∙ cong (_∷_ y) p)

comm-++ : ∀ (xs ys : FMSet A) → xs ++ ys ≡ ys ++ xs
comm-++ = ElimProp.f (isPropΠ (λ _ → trunc _ _))
  (λ ys → sym (unitr-++ ys))
  (λ x {xs} p ys → cong (x ∷_) (p ys)
                 ∙ cong (_++ xs) (cons-++ x ys)
                 ∙ sym (assoc-++ ys [ x ] xs))

module FMSetUniversal {ℓ} {M : Type ℓ} (MSet : isSet M)
  (e : M) (_⊗_ : M → M → M)
  (comm-⊗ : ∀ x y → x ⊗ y ≡ y ⊗ x) (assoc-⊗ : ∀ x y z → x ⊗ (y ⊗ z) ≡ (x ⊗ y) ⊗ z)
  (unit-⊗ : ∀ x → e ⊗ x ≡ x)
  (f : A → M) where

  f-extend : FMSet A → M
  f-extend = Rec.f MSet e (λ x m → f x ⊗ m)
         (λ x y m → comm-⊗ (f x) (f y ⊗ m) ∙ sym (assoc-⊗ (f y) m (f x)) ∙ cong (f y ⊗_) (comm-⊗ m (f x)))

  f-extend-nil : f-extend [] ≡ e
  f-extend-nil = refl

  f-extend-cons : ∀ x xs → f-extend (x ∷ xs) ≡ f x ⊗ f-extend xs
  f-extend-cons x xs = refl

  f-extend-sing : ∀ x → f-extend [ x ] ≡ f x
  f-extend-sing x = comm-⊗ (f x) e ∙ unit-⊗ (f x)

  f-extend-++ : ∀ xs ys → f-extend (xs ++ ys) ≡ f-extend xs ⊗ f-extend ys
  f-extend-++ = ElimProp.f (isPropΠ λ _ → MSet _ _)
    (λ ys → sym (unit-⊗ (f-extend ys)))
    (λ x {xs} p ys → cong (f x ⊗_) (p ys) ∙ assoc-⊗ (f x) (f-extend xs) (f-extend ys))

  module _ (h : FMSet A → M) (h-nil : h [] ≡ e) (h-sing : ∀ x → h [ x ] ≡ f x)
           (h-++ : ∀ xs ys → h (xs ++ ys) ≡ h xs ⊗ h ys) where

    f-extend-unique : h ≡ f-extend
    f-extend-unique = funExt (ElimProp.f (MSet _ _)
                              h-nil
                              (λ x {xs} p → (h-++ [ x ] xs) ∙ cong (_⊗ h xs) (h-sing x) ∙ cong (f x ⊗_) p))



-- We want to construct a multiset-structure on FMSet A, the empty set and insertion are given by the constructors,
-- for the membership part we use the recursor

-- Is there a way around the auxillary functions with the with-syntax?
FMSmember-∷*-aux : (a x : A) → Dec (a ≡ x) → ℕ → ℕ
FMSmember-∷*-aux a x (yes a≡x) n = suc n
FMSmember-∷*-aux a x (no  a≢x) n = n


FMSmember-comm*-aux :  (a x y : A) (n : ℕ) (p : Dec (a ≡ x)) (q : Dec (a ≡ y))
                     →  FMSmember-∷*-aux a x p (FMSmember-∷*-aux a y q n)
                      ≡ FMSmember-∷*-aux a y q (FMSmember-∷*-aux a x p n)
FMSmember-comm*-aux a x y n (yes a≡x) (yes a≡y) = refl
FMSmember-comm*-aux a x y n (yes a≡x) (no  a≢y) = refl
FMSmember-comm*-aux a x y n (no  a≢x) (yes a≡y) = refl
FMSmember-comm*-aux a x y n (no  a≢x) (no  a≢y) = refl


-- If A has decidable equality we can define the member-function:
module _(discA : Discrete A) where
 FMSmember-∷* : A → A → ℕ → ℕ
 FMSmember-∷* a x n = FMSmember-∷*-aux a x (discA a x) n

 FMSmember-comm* :  (a x y : A) (n : ℕ)
                  →  FMSmember-∷* a x (FMSmember-∷* a y n)
                   ≡ FMSmember-∷* a y (FMSmember-∷* a x n)
 FMSmember-comm* a x y n = FMSmember-comm*-aux a x y n (discA a x) (discA a y)

 FMSmember : A → FMSet A → ℕ
 FMSmember a = Rec.f isSetℕ 0 (FMSmember-∷* a) (FMSmember-comm* a)


 FMS-with-str : Multi-Set A (Discrete→isSet discA)
 FMS-with-str = (FMSet A , [] , _∷_ , FMSmember)

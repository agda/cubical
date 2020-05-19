{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.FiniteMultiset.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat
open import Cubical.Data.Empty as ⊥
open import Cubical.Relation.Nullary
open import Cubical.HITs.FiniteMultiset.Base
open import Cubical.Structures.MultiSet
open import Cubical.Relation.Nullary.DecidableEq

private
  variable
    ℓ : Level
    A : Type ℓ

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
-- for the count part we use the recursor

-- Is there a way around the auxillary functions with the with-syntax?
FMScount-∷*-aux : (a x : A) → Dec (a ≡ x) → ℕ → ℕ
FMScount-∷*-aux a x (yes a≡x) n = suc n
FMScount-∷*-aux a x (no  a≢x) n = n


FMScount-comm*-aux :  (a x y : A) (n : ℕ) (p : Dec (a ≡ x)) (q : Dec (a ≡ y))
                     →  FMScount-∷*-aux a x p (FMScount-∷*-aux a y q n)
                      ≡ FMScount-∷*-aux a y q (FMScount-∷*-aux a x p n)
FMScount-comm*-aux a x y n (yes a≡x) (yes a≡y) = refl
FMScount-comm*-aux a x y n (yes a≡x) (no  a≢y) = refl
FMScount-comm*-aux a x y n (no  a≢x) (yes a≡y) = refl
FMScount-comm*-aux a x y n (no  a≢x) (no  a≢y) = refl


-- If A has decidable equality we can define the count-function:
module _(discA : Discrete A) where
 FMScount-∷* : A → A → ℕ → ℕ
 FMScount-∷* a x n = FMScount-∷*-aux a x (discA a x) n

 FMScount-comm* :  (a x y : A) (n : ℕ)
                  →  FMScount-∷* a x (FMScount-∷* a y n)
                   ≡ FMScount-∷* a y (FMScount-∷* a x n)
 FMScount-comm* a x y n = FMScount-comm*-aux a x y n (discA a x) (discA a y)

 FMScount : A → FMSet A → ℕ
 FMScount a = Rec.f isSetℕ 0 (FMScount-∷* a) (FMScount-comm* a)


 FMS-with-str : Multi-Set A (Discrete→isSet discA)
 FMS-with-str = (FMSet A , [] , _∷_ , FMScount)



 -- We prove some useful properties of the FMScount function
 FMScount-≡-lemma : ∀ {a} {x} xs → a ≡ x → FMScount a (x ∷ xs) ≡ suc (FMScount a xs)
 FMScount-≡-lemma {a} {x} xs a≡x with discA a x
 ...                         | yes _   = refl
 ...                         | no  a≢x = ⊥.rec (a≢x a≡x)


 FMScount-≡-lemma-refl : ∀ {x} xs → FMScount x (x ∷ xs) ≡ suc (FMScount x xs)
 FMScount-≡-lemma-refl {x} xs = FMScount-≡-lemma xs refl


 FMScount-≢-lemma : ∀ {a} {x} xs → ¬ a ≡ x → FMScount a (x ∷ xs) ≡ FMScount a xs
 FMScount-≢-lemma {a} {x} xs a≢x with discA a x
 ...                         | yes a≡x = ⊥.rec (a≢x a≡x)
 ...                         | no  _   = refl


 FMScount-0-lemma : ∀ xs → (∀ a → FMScount a xs ≡ 0) → xs ≡ []
 FMScount-0-lemma = ElimProp.f (isPropΠ λ _ → trunc _ _) (λ _ → refl) θ
  where
  θ : ∀ x {xs} → ((∀ a → FMScount a xs ≡ 0) → xs ≡ [])
               → ((∀ a → FMScount a (x ∷ xs) ≡ 0) → (x ∷ xs) ≡ [])
  θ x {xs} _ p = ⊥.rec (snotz (sym (FMScount-≡-lemma-refl xs) ∙ p x))


 -- we define a function that removes an element a from a finite multiset once
 -- by simultaneously defining two lemmas about it
 remove1 : A → FMSet A → FMSet A
 remove1 a [] = []
 remove1 a (x ∷ xs) with (discA a x)
 ...               | yes _ = xs
 ...               | no  _ = x ∷ remove1 a xs
 remove1 a (comm x y xs i) = path i
  where
  path : remove1 a (x ∷ y ∷ xs) ≡ remove1 a (y ∷ x ∷ xs)
  path with discA a x with discA a y
  path | yes a≡x      | yes a≡y = λ i → ((sym a≡y ∙ a≡x) i) ∷ xs
  path | yes a≡x      | no  _   = λ i → y ∷ (eq i)
   where
   eq : xs ≡ remove1 a (x ∷ xs)
   eq with discA a x
   eq | yes _   = refl
   eq | no  a≢x = ⊥.rec (a≢x a≡x)
  path | no  _        | yes a≡y = λ i → x ∷ (eq i)
   where
   eq : remove1 a (y ∷ xs) ≡ xs
   eq with discA a y
   eq | yes _   = refl
   eq | no  a≢y = ⊥.rec (a≢y a≡y)
  path | no  a≢x      | no  a≢y = (λ i → x ∷ (p i)) ∙∙ comm x y (remove1 a xs) ∙∙ (λ i → y ∷ (sym q i))
   where
    p : remove1 a (y ∷ xs) ≡ y ∷ (remove1 a xs)
    p with discA a y
    p | yes a≡y = ⊥.rec (a≢y a≡y)
    p | no  _   = refl
    q : remove1 a (x ∷ xs) ≡ x ∷ (remove1 a xs)
    q with discA a x
    q | yes a≡x = ⊥.rec (a≢x a≡x)
    q | no  _   = refl
 remove1 a (trunc xs ys p q i j) = trunc (remove1 a xs) (remove1 a ys) (cong (remove1 a) p) (cong (remove1 a) q) i j


 remove1-≡-lemma : ∀ {a} {x} xs → a ≡ x → xs ≡ remove1 a (x ∷ xs)
 remove1-≡-lemma {a} {x} xs a≡x with discA a x
 ...                            | yes _   = refl
 ...                            | no  a≢x = ⊥.rec (a≢x a≡x)

 remove1-≢-lemma : ∀ {a} {x} xs → ¬ a ≡ x → remove1 a (x ∷ xs) ≡ x ∷ remove1 a xs
 remove1-≢-lemma {a} {x} xs a≢x with discA a x
 ...                            | yes a≡x = ⊥.rec (a≢x a≡x)
 ...                            | no  _   = refl


 remove1-predℕ-lemma : ∀ a xs → FMScount a (remove1 a xs) ≡ predℕ (FMScount a xs)
 remove1-predℕ-lemma a = ElimProp.f (isSetℕ _ _) refl θ
  where
  θ : ∀ x {xs} → FMScount a (remove1 a xs) ≡ predℕ (FMScount a xs)
               → FMScount a (remove1 a (x ∷ xs)) ≡ predℕ (FMScount a (x ∷ xs))
  θ x {xs} p with discA a x
  ...        | yes _   = refl
  ...        | no  a≢x = FMScount-≢-lemma (remove1 a xs) a≢x ∙ p


 remove1-zero-lemma : ∀ a xs → FMScount a xs ≡ zero → xs ≡ remove1 a xs
 remove1-zero-lemma a = ElimProp.f (isPropΠ λ _ → trunc _ _) (λ _ → refl) θ
  where
  θ : ∀ x {xs} → (FMScount a xs ≡ zero → xs ≡ remove1 a xs)
               → FMScount a (x ∷ xs) ≡ zero → x ∷ xs ≡ remove1 a (x ∷ xs)
  θ x {xs} hyp p with discA a x
  ...            | yes _ = ⊥.rec (snotz p)
  ...            | no  _ = cong (x ∷_) (hyp p)


 remove1-suc-lemma : ∀ a n xs → FMScount a xs ≡ suc n → xs ≡ a ∷ (remove1 a xs)
 remove1-suc-lemma a n = ElimProp.f (isPropΠ λ _ → trunc _ _) (λ p → ⊥.rec (znots p)) θ
  where
  θ : ∀ x {xs} → (FMScount a xs ≡ suc n → xs ≡ a ∷ (remove1 a xs))
               → FMScount a (x ∷ xs) ≡ suc n → x ∷ xs ≡ a ∷ (remove1 a (x ∷ xs))
  θ x {xs} hyp p with discA a x
  ...            | yes a≡x = (λ i → (sym a≡x i) ∷ xs)
  ...            | no  a≢x = cong (x ∷_) (hyp p) ∙ comm x a (remove1 a xs)


 FMScount-remove1-≢-lemma : ∀ {a} {x} xs → ¬ a ≡ x → FMScount a (remove1 x xs) ≡ FMScount a xs
 FMScount-remove1-≢-lemma {a} {x} xs a≢x with discreteℕ (FMScount x xs) zero
 ...                     | yes p = cong (FMScount a) (sym (remove1-zero-lemma x xs p))
 ...                     | no ¬p = sym (FMScount-≢-lemma (remove1 x xs) a≢x) ∙ cong (FMScount a) eq₁
   where
   eq₁ : (x ∷ remove1 x xs) ≡ xs
   eq₁ = sym (remove1-suc-lemma x (predℕ (FMScount x xs)) xs (suc-predℕ (FMScount x xs) ¬p))

{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.AssocList.Base where

open import Cubical.Foundations.Everything
open import Cubical.Data.Nat   using (ℕ; _+_)

private
  variable
    ℓ : Level
    A : Type ℓ

infixr 5 ⟨_,_⟩∷_




data AssocList (A : Type ℓ) : Type ℓ where
 ⟨⟩ : AssocList A
 ⟨_,_⟩∷_ : (a : A) (n : ℕ) (xs : AssocList A) → AssocList A
 per : ∀ a b xs →   ⟨ a , 1 ⟩∷ ⟨ b , 1 ⟩∷ xs
                  ≡ ⟨ b , 1 ⟩∷ ⟨ a , 1 ⟩∷ xs
 agg : ∀ a m n xs →  ⟨ a , m ⟩∷ ⟨ a , n ⟩∷ xs
                   ≡ ⟨ a , m + n ⟩∷ xs
 del : ∀ a xs → ⟨ a , 0 ⟩∷ xs ≡ xs
 trunc : isSet (AssocList A)

pattern ⟨_⟩ a = ⟨ a , 1 ⟩∷ ⟨⟩





--Elimination and recursion principle for association lists
module Elim {ℓ'} {B : AssocList A → Type ℓ'}
       (⟨⟩* : B ⟨⟩) (⟨_,_⟩∷*_ : (x : A) (n : ℕ) {xs : AssocList A} → B xs → B (⟨ x , n ⟩∷ xs))
       (per* :  (x y : A) {xs : AssocList A} (b : B xs)
              → PathP (λ i → B (per x y xs i)) (⟨ x , 1 ⟩∷* ⟨ y , 1 ⟩∷* b) (⟨ y , 1 ⟩∷* ⟨ x , 1 ⟩∷* b))
       (agg* :  (x : A) (m n : ℕ) {xs : AssocList A} (b : B xs)
              → PathP (λ i → B (agg x m n xs i)) (⟨ x , m ⟩∷* ⟨ x , n ⟩∷* b) (⟨ x , m + n ⟩∷* b))
       (del* :  (x : A) {xs : AssocList A} (b : B xs)
              → PathP (λ i → B (del x xs i)) (⟨ x , 0 ⟩∷* b) b)
       (trunc* : (xs : AssocList A) → isSet (B xs)) where

 f : (xs : AssocList A) → B xs
 f ⟨⟩ = ⟨⟩*
 f (⟨ a , n ⟩∷ xs) = ⟨ a , n ⟩∷* f xs
 f (per a b xs i) = per* a b (f xs) i
 f (agg a m n xs i) = agg* a m n (f xs) i
 f (del a xs i) = del* a (f xs) i
 f (trunc xs ys p q i j) = isOfHLevel→isOfHLevelDep 2 trunc*  (f xs) (f ys) (cong f p) (cong f q) (trunc xs ys p q) i j



module ElimProp {ℓ'} {B : AssocList A → Type ℓ'} (BProp : {xs : AssocList A} → isProp (B xs))
       (⟨⟩* : B ⟨⟩) (⟨_,_⟩∷*_ : (x : A) (n : ℕ) {xs : AssocList A} → B xs → B (⟨ x , n ⟩∷ xs)) where

 f : (xs : AssocList A) → B xs
 f = Elim.f ⟨⟩* ⟨_,_⟩∷*_
      (λ x y {xs} b → toPathP (BProp (transp (λ i → B (per x y xs i)) i0 (⟨ x , 1 ⟩∷* ⟨ y , 1 ⟩∷* b)) (⟨ y , 1 ⟩∷* ⟨ x , 1 ⟩∷* b)))
      (λ x m n {xs} b → toPathP (BProp (transp (λ i → B (agg x m n xs i)) i0 (⟨ x , m ⟩∷* ⟨ x , n ⟩∷* b)) (⟨ x , m + n ⟩∷* b)))
      (λ x {xs} b → toPathP (BProp (transp (λ i → B (del x xs i)) i0 (⟨ x , 0 ⟩∷* b)) b))
      (λ xs → isProp→isSet BProp)



module Rec {ℓ'} {B : Type ℓ'} (BType : isSet B)
       (⟨⟩* : B) (⟨_,_⟩∷*_ : (x : A) (n : ℕ) → B → B)
       (per* :  (x y : A) (b : B) → (⟨ x , 1 ⟩∷* ⟨ y , 1 ⟩∷* b) ≡ (⟨ y , 1 ⟩∷* ⟨ x , 1 ⟩∷* b))
       (agg* :  (x : A) (m n : ℕ) (b : B) → (⟨ x , m ⟩∷* ⟨ x , n ⟩∷* b) ≡ (⟨ x , m + n ⟩∷* b))
       (del* :  (x : A) (b : B) → (⟨ x , 0 ⟩∷* b) ≡ b) where

 f : AssocList A → B
 f = Elim.f ⟨⟩* (λ x n b → ⟨ x , n ⟩∷* b) (λ x y b → per* x y b) (λ x m n b → agg* x m n b) (λ x b → del* x b) (λ _ → BType)

{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.FiniteMultiset.Order where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum
open import Cubical.Relation.Nullary
open import Cubical.HITs.FiniteMultiset.Base
open import Cubical.HITs.FiniteMultiset.Properties as FMS
open import Cubical.Structures.MultiSet
open import Cubical.Relation.Nullary.DecidableEq


private
 variable
  A : Type₀

module _(discA : Discrete A) where
 _≼_ : FMSet A → FMSet A → Type₀ --\preceq
 xs ≼ ys = ∀ a → FMScount discA a xs ≤ FMScount discA a ys

 ≼-refl : ∀ xs → xs ≼ xs
 ≼-refl xs a  = ≤-refl
 
 ≼-trans : ∀ xs ys zs → xs ≼ ys → ys ≼ zs → xs ≼ zs
 ≼-trans xs ys zs xs≼ys ys≼zs a = ≤-trans (xs≼ys a) (ys≼zs a)

 
 ≼[]→≡[] : ∀ xs → xs ≼ [] → xs ≡ []
 ≼[]→≡[] xs xs≼[] = FMScount-0-lemma discA xs λ a → ≤0→≡0 (xs≼[] a)


 

 ≼-remove1 : ∀ a xs → remove1 discA a xs ≼ xs
 ≼-remove1 a xs b with discA a b
 ...              | yes a≡b = subst (λ n → n ≤ FMScount discA b xs) (sym path) (≤-predℕ)
  where
  path : FMScount discA b (remove1 discA a xs) ≡ predℕ (FMScount discA b xs)
  path = cong (λ c → FMScount discA b (remove1 discA c xs)) a≡b ∙ remove1-predℕ-lemma discA b xs
 ...              | no  a≢b = subst (λ n → n ≤ FMScount discA b xs) (sym path) ≤-refl
  where
  path : FMScount discA b (remove1 discA a xs) ≡ FMScount discA b xs
  path with discreteℕ (FMScount discA a xs) zero
  path | yes p = cong (FMScount discA b) (sym (remove1-zero-lemma discA a xs p))
  path | no ¬p = sym (FMScount-≢-lemma discA  (remove1 discA a xs) λ b≡a → a≢b (sym b≡a)) ∙ cong (FMScount discA b) eq₁
   where
   eq₁ : (a ∷ remove1 discA a xs) ≡ xs
   eq₁ = sym (remove1-suc-lemma discA a (predℕ (FMScount discA a xs)) xs (suc-predℕ (FMScount discA a xs) ¬p))


 ≼-remove1-lemma : ∀ x xs ys → ys ≼ (x ∷ xs) → (remove1 discA x ys) ≼ xs
 ≼-remove1-lemma x xs ys ys≼x∷xs a with discA a x
 ...                               | yes a≡x = ≤-trans (≤-trans (0 , p₁) (predℕ-≤-predℕ (ys≼x∷xs a)))
                                                                (0 , cong predℕ (FMScount-≡-lemma discA xs a≡x))
  where
  p₁ : FMScount discA a (remove1 discA x ys) ≡ predℕ (FMScount discA a ys)
  p₁ = subst (λ b →  FMScount discA a (remove1 discA b ys) ≡ predℕ (FMScount discA a ys)) a≡x (remove1-predℕ-lemma discA a ys)
  
 ...                               | no  a≢x = ≤-trans (≤-trans (0 , p₁) (ys≼x∷xs a)) (0 , FMScount-≢-lemma discA  xs a≢x) -- extra lemma ≡→≤?
  where
  -- have as extra lemma!!
  p₁ : FMScount discA a (remove1 discA x ys) ≡ FMScount discA a ys
  p₁ with discreteℕ (FMScount discA x ys) zero
  p₁ | yes p = cong (FMScount discA a) (sym (remove1-zero-lemma discA x ys p))
  p₁ | no ¬p = sym (FMScount-≢-lemma discA (remove1 discA x ys) a≢x) ∙ cong (FMScount discA a) eq₁
   where
   eq₁ : (x ∷ remove1 discA x ys) ≡ ys
   eq₁ = sym (remove1-suc-lemma discA x (predℕ (FMScount discA x ys)) ys (suc-predℕ (FMScount discA x ys) ¬p))



 ≼-Dichotomy : ∀ x xs ys → ys ≼ (x ∷ xs) → (ys ≼ xs) ⊎ (ys ≡ x ∷ (remove1 discA x ys))
 ≼-Dichotomy x xs ys ys≼x∷xs with (FMScount discA x ys) ≟ suc (FMScount discA x xs)
 ...                         | lt <suc = inl ys≼xs
  where
  ys≼xs : ys ≼ xs
  ys≼xs a with discA a x
  ...     | yes a≡x = pred-≤-pred (subst (λ b → (FMScount discA b ys) < suc (FMScount discA b xs)) (sym a≡x) <suc)
  ...     | no  a≢x = ≤-trans (ys≼x∷xs a) (subst (λ n → FMScount discA a (x ∷ xs) ≤ n) (FMScount-≢-lemma discA xs a≢x) ≤-refl)
 ...                         | eq ≡suc = inr (remove1-suc-lemma discA x (FMScount discA x xs) ys ≡suc)
 ...                         | gt >suc = ⊥.rec (¬m<m strict-ineq)
  where
  strict-ineq : suc (FMScount discA x xs) < suc (FMScount discA x xs)
  strict-ineq =  <≤-trans (<≤-trans >suc (ys≼x∷xs x)) (0 , FMScount-≡-lemma-refl discA xs)




 module FMS-≼-ElimProp {ℓ} {B : FMSet A → Type ℓ}
                       (BisProp : ∀ {xs} → isProp (B xs)) (b₀ : B [])
                       (B-≼-hyp : ∀ x xs → (∀ ys → ys ≼ xs → B ys) → B (x ∷ xs)) where

  C : FMSet A → Type ℓ
  C xs = ∀ ys → ys ≼ xs → B ys

  obs : (∀ xs → C xs) → (∀ xs → B xs)
  obs C-hyp xs = C-hyp xs xs (≼-refl xs)

  g : ∀ xs → C xs
  g = ElimProp.f (isPropΠ2 (λ _ _ → BisProp)) c₀ θ
   where
   c₀ : C []
   c₀ ys ys≼[] = subst B (sym (≼[]→≡[] ys ys≼[])) b₀

   θ : ∀ x {xs} → C xs → C (x ∷ xs)
   θ x {xs} hyp ys ys≼x∷xs with ≼-Dichotomy x xs ys ys≼x∷xs
   ...                     | inl ys≼xs   = hyp ys ys≼xs
   ...                     | inr ys≡x∷zs = subst B (sym ys≡x∷zs) (B-≼-hyp x zs χ)
    where
    zs = remove1 discA x ys
    χ : ∀ vs → vs ≼ zs → B vs
    χ vs vs≼zs = hyp vs (≼-trans vs zs xs vs≼zs (≼-remove1-lemma x xs ys ys≼x∷xs))

  f : ∀ xs → B xs
  f = obs g



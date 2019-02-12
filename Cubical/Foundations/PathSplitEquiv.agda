{-

Theory about path split equivalences. 
They are convenient to construct localization HITs as in 
(the "modalities paper")
https://arxiv.org/abs/1706.07526

-}
{-# OPTIONS --cubical --safe #-}
module Cubical.Foundations.PathSplitEquiv where

open import Agda.Primitive

open import Cubical.Core.Everything

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence


isEquivCong : ∀ {ℓ} {A B : Set ℓ} {x y : A} (e : A ≃ B) → isEquiv (λ (p : x ≡ y) → (cong (fst e) p))
isEquivCong e = EquivJ (λ (B' A' : Set _) (e' : A' ≃ B') →
                         (x' y' : A') → isEquiv (λ (p : x' ≡ y') → cong (fst e') p))
                       (λ _ x' y' → idIsEquiv (x' ≡ y')) _ _ e _ _



congEquiv : ∀ {ℓ} {A B : Set ℓ} {x y : A} (e : A ≃ B) → (x ≡ y) ≃ (e .fst x ≡ e .fst y)
congEquiv e = ((λ (p : _ ≡ _) → cong (fst e) p) , isEquivCong e)

isEquivPreComp : ∀ {ℓ ℓ′} {A B : Set ℓ} {C : Set ℓ′} (e : A ≃ B)
  → isEquiv (λ (φ : B → C) → (λ (x : A) → φ (e .fst x)))
isEquivPreComp {A = A} {C = C} e = EquivJ
                  (λ (B A : Set _) (e' : A ≃ B) → isEquiv (λ (φ : B → C) → (λ (x : A) → φ (e' .fst x))))
                  (λ A → idIsEquiv (A → C)) _ _ e

isEquivPostComp : ∀ {ℓ ℓ′} {A B : Set ℓ} {C : Set ℓ′} (e : A ≃ B)
  → isEquiv (λ (φ : C → A) → (λ (x : C) → e .fst (φ x)))
isEquivPostComp {A = A} {C = C} e = EquivJ
                  (λ (B A : Set _) (e' : A ≃ B) →  isEquiv (λ (φ : C → A) → (λ (x : C) → e' .fst (φ x))))
                  (λ A → idIsEquiv (C → A)) _ _ e

preCompEquiv : ∀ {ℓ ℓ′} {A B : Set ℓ} {C : Set ℓ′} (e : A ≃ B)
             → (B → C) ≃ (A → C)
preCompEquiv e = (λ φ x → φ (fst e x)) , isEquivPreComp e

postCompEquiv : ∀ {ℓ ℓ′} {A B : Set ℓ} {C : Set ℓ′} (e : A ≃ B)
             → (C → A) ≃ (C → B)
postCompEquiv e = (λ φ x → fst e (φ x)) , isEquivPostComp e

record isPathSplitEquiv {ℓ ℓ'} {A : Set  ℓ} {B : Set ℓ'} (f : A → B) : Set (ℓ ⊔ ℓ') where
  field
    s : B → A 
    sec : section f s
    secCong : (x y : A) → Σ[ s' ∈ (f(x) ≡ f(y) → x ≡ y) ] section (cong f) s'

PathSplitEquiv : ∀ {ℓ ℓ'} (A : Set  ℓ) (B : Set ℓ') → Set (ℓ ⊔ ℓ')
PathSplitEquiv A B = Σ[ f ∈ (A → B) ] isPathSplitEquiv f

open isPathSplitEquiv 

idIsPathSplitEquiv : ∀ {ℓ} {A : Set ℓ} → isPathSplitEquiv (λ (x : A) → x)
s idIsPathSplitEquiv x = x
sec idIsPathSplitEquiv x = refl
secCong idIsPathSplitEquiv = λ x y → (λ p → p) , λ p _ → p

module _ {ℓ} {A B : Set ℓ} where
  toIsEquiv : (f : A → B) → isPathSplitEquiv f → isEquiv f 
  toIsEquiv f record { s = s ; sec = sec ; secCong = secCong } =
    (isoToEquiv (f , record {
                            inverse = s ;
                            rightInv = sec ;
                            leftInv = λ x → (secCong (s (f x)) x).fst (sec (f x))})) .snd
                          
  sectionOfEquiv' : (f : A → B) → isEquiv f → B → A
  sectionOfEquiv' f record { equiv-proof = all-fibers-contractible } x =
    all-fibers-contractible x .fst .fst

  isSec : (f : A → B) → (pf : isEquiv f) → section f (sectionOfEquiv' f pf)
  isSec f record { equiv-proof = all-fibers-contractible } x =
    all-fibers-contractible x .fst .snd 

  sectionOfEquiv : (f : A → B) → isEquiv f → Σ (B → A) (section f)
  sectionOfEquiv f e = sectionOfEquiv' f e , isSec f e

module _ {ℓ} {A B : Set ℓ} where
  abstract
    fromIsEquiv : (f : A → B) → isEquiv f → isPathSplitEquiv f
    s (fromIsEquiv f pf) = sectionOfEquiv' f pf
    sec (fromIsEquiv f pf) = isSec f pf
    secCong (fromIsEquiv f pf) x y = sectionOfEquiv cong-f eq-cong
            where
            cong-f : x ≡ y → f x ≡ f y
            cong-f = λ (p : x ≡ y) → cong f p
            eq-cong : isEquiv cong-f
            eq-cong = isEquivCong (f , pf)

  pathSplitToEquiv : PathSplitEquiv A B → A ≃ B
  fst (pathSplitToEquiv (f , _)) = f
  snd (pathSplitToEquiv (_ , e)) = toIsEquiv _ e

  equivToPathSplit : A ≃ B → PathSplitEquiv A B
  fst (equivToPathSplit (f , _)) = f
  snd (equivToPathSplit (_ , e)) = fromIsEquiv _ e

{- 
  PathSplitEquiv is a proposition
-}
module _ {ℓ} {A B : Set ℓ} (f : A → B) where
{-
  equivHasUniqueSections :
    isEquiv f → isContr (Σ (B → A) (section f))
  equivHasUniqueSections eq = equiv-proof (snd (postCompEquiv (f , eq))) (λ (x : B) → x)
  
  isPropIsPathSplitEquiv : 
     isProp (isPathSplitEquiv f)
  isPropIsPathSplitEquiv f = {!!}
-}

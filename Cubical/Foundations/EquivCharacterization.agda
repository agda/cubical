{-

More Theory about equivalences/different characterizations of equivalence

- 'cong f' is an equivalence, if f is an equivalence

-}
{-# OPTIONS --cubical --safe #-}

module Cubical.Foundations.EquivCharacterization where

open import Cubical.Core.Everything

open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv

isEquivCong : ∀ {ℓ} {A B : Set ℓ} {x y : A} (e : A ≃ B) → isEquiv (λ (p : x ≡ y) → (cong (e .fst) p))
isEquivCong e = EquivJ (λ (B' A' : Set _) (e' : A' ≃ B') →
                         (x' y' : A') → isEquiv (λ (p : x' ≡ y') → cong (e' .fst) p))
                       (λ _ x' y' → idIsEquiv (x' ≡ y')) _ _ e _ _

congEquiv : ∀ {ℓ} {A B : Set ℓ} {x y : A} (e : A ≃ B) → (x ≡ y) ≃ (e .fst x ≡ e .fst y)
congEquiv e = ((λ (p : _ ≡ _) → cong (e .fst) p) , isEquivCong e)

record isPathSplitEquiv {ℓ} {A B : Set  ℓ} (f : A → B) : Set ℓ where
  field
    s : B → A 
    isSection : section f s
    isSectionCong : (x y : A) → Σ[ s' ∈ (f(x) ≡ f(y) → x ≡ y) ] section (cong f) s'

idIsPathSplitEquiv : ∀ {ℓ} {A : Set ℓ} → isPathSplitEquiv (λ (x : A) → x)
idIsPathSplitEquiv = record {
                       s = λ x → x ;
                       isSection = λ x → refl ;
                       isSectionCong = λ x y → (λ p → p) , λ p _ → p
                     }


module _ {ℓ} {A B : Set ℓ} where
  toIsEquiv : (f : A → B) → isPathSplitEquiv f → isEquiv f 
  toIsEquiv f record { s = r ; isSection = isSection ; isSectionCong = isSectionCong } =
    (isoToEquiv f r isSection λ (x : A) → (isSectionCong (r (f x)) x).fst (isSection (f x))) .snd

  sectionOfEquiv : {A' B' : Set ℓ} → (f : A' → B') → isEquiv f → B' → A'
  sectionOfEquiv f record { equiv-proof = all-fibers-contractible } x =
    all-fibers-contractible x .fst .fst

  isSection : {A' B' : Set ℓ} → (f : A' → B') → (pf : isEquiv f) → section f (sectionOfEquiv f pf)
  isSection f record { equiv-proof = all-fibers-contractible } =
    λ x → all-fibers-contractible x .fst .snd 

  fromIsEquiv : (f : A → B) → isEquiv f → isPathSplitEquiv f
  fromIsEquiv f pf = 
    record {
      s = sectionOfEquiv f pf ;
      isSection = isSection f pf ;
      isSectionCong = λ x y
        → sectionOfEquiv (cong f) (isEquivCong (f , pf)) , isSection (cong f) (isEquivCong (f , pf))
    }

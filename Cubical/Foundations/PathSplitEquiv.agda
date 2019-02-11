{-

Theory about equivalences (definitions are in Core/Glue.agda)

- isEquiv is a proposition ([isPropIsEquiv])
- Any isomorphism is an equivalence ([isoToEquiv])
- transport is an equivalence ([transportEquiv])

-}
{-# OPTIONS --cubical --safe #-}
module Cubical.Foundations.PathSplitEquiv where

open import Cubical.Core.Everything

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence


isEquivCong : ∀ {ℓ} {A B : Set ℓ} {x y : A} (e : A ≃ B) → isEquiv (λ (p : x ≡ y) → (cong (e .fst) p))
isEquivCong e = EquivJ (λ (B' A' : Set _) (e' : A' ≃ B') →
                         (x' y' : A') → isEquiv (λ (p : x' ≡ y') → cong (e' .fst) p))
                       (λ _ x' y' → idIsEquiv (x' ≡ y')) _ _ e _ _

congEquiv : ∀ {ℓ} {A B : Set ℓ} {x y : A} (e : A ≃ B) → (x ≡ y) ≃ (e .fst x ≡ e .fst y)
congEquiv e = ((λ (p : _ ≡ _) → cong (e .fst) p) , isEquivCong e)

{-
  Everything about path split equivalences is from https://arxiv.org/abs/1706.07526
-}
record isPathSplitEquiv {ℓ} {A B : Set  ℓ} (f : A → B) : Set ℓ where
  field
    s : B → A 
    sec : section f s
    secCong : (x y : A) → Σ[ s' ∈ (f(x) ≡ f(y) → x ≡ y) ] section (cong f) s'

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
                            leftInv = λ (x : A) → (secCong (s (f x)) x).fst (sec (f x))})) .snd

  sectionOfEquiv : {A' B' : Set ℓ} → (f : A' → B') → isEquiv f → B' → A'
  sectionOfEquiv f record { equiv-proof = all-fibers-contractible } x =
    all-fibers-contractible x .fst .fst

  isSec : {A' B' : Set ℓ} → (f : A' → B') → (pf : isEquiv f) → section f (sectionOfEquiv f pf)
  isSec f record { equiv-proof = all-fibers-contractible } x =
    all-fibers-contractible x .fst .snd 

  fromIsEquiv : (f : A → B) → isEquiv f → isPathSplitEquiv f
  s (fromIsEquiv f pf) = sectionOfEquiv f pf
  sec (fromIsEquiv f pf) = isSec f pf
  secCong (fromIsEquiv f pf) x y = 
        (sectionOfEquiv {x ≡ y} {f x ≡ f y} cong-f eq-cong
          , isSec {x ≡ y} {f x ≡ f y} cong-f eq-cong)
        where
          cong-f : x ≡ y → f x ≡ f y
          cong-f = λ (p : x ≡ y) → cong f p
          eq-cong : isEquiv cong-f
          eq-cong = isEquivCong (f , pf)

  

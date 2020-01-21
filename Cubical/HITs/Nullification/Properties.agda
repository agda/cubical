{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.Nullification.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.PathSplitEquiv
open isPathSplitEquiv

open import Cubical.HITs.Nullification.Base

rec : ∀ {ℓ ℓ' ℓ''} {S : Type ℓ} {A : Type ℓ'} {B : Type ℓ''}
      → (nB : isNull S B) → (A → B) → Null S A → B
rec nB g ∣ x ∣ = g x
rec nB g (ext f) = fst (sec nB) (λ s → rec nB g (f s))
rec nB g (isExt f s i) = snd (sec nB) (λ s → rec nB g (f s)) i s
rec nB g (≡ext {x} {y} p i) = fst (secCong nB (rec nB g x) (rec nB g y)) (λ i s → rec nB g (p s i)) i
rec nB g (≡isExt {x} {y} p s i j) = snd (secCong nB (rec nB g x) (rec nB g y)) (λ i s → rec nB g (p s i)) i j s

toPathP⁻ : ∀ {ℓ} (A : I → Type ℓ) {x : A i0} {y : A i1} → x ≡ transport⁻ (λ i → A i) y → PathP A x y
toPathP⁻ A p i = toPathP {A = λ i → A (~ i)} (sym p) (~ i)

toPathP⁻-sq : ∀ {ℓ} {A : Type ℓ} (x : A) → Square (toPathP⁻ (λ _ → A) (λ _ → transport refl x)) refl
                                                  (transportRefl x) refl
toPathP⁻-sq x j i = hcomp (λ l → λ { (i = i0) → transportRefl x j
                                   ; (i = i1) → x ; (j = i1) → x })
                          (transportRefl x (i ∨ j))

module _ {ℓ ℓ' ℓ''} {S : Type ℓ} {A : Type ℓ'} {B : Null S A → Type ℓ''} where

  private
    secCongDep' : ∀ (nB : (x : Null S A) → isNull S (B x)) {x y : Null S A} (p : x ≡ y)
                  → (∀ (bx : B x) (by : B y) → hasSection (cong₂ (λ x (b : B x) (_ : S) → b) p))
    secCongDep' nB p = secCongDep (λ _ → const) p (λ a → secCong (nB a))

  ind : (nB : (x : Null S A) → isNull S (B x)) → ((a : A) → B ∣ a ∣) → (x : Null S A) → B x
  ind nB g ∣ x ∣ = g x
  ind nB g (ext f)
    = fst (sec (nB (ext f)))
          (λ s → transport (λ i → B (isExt f s (~ i))) (ind nB g (f s)))

  ind nB g (isExt f s i)
    = toPathP⁻ (λ i → B (isExt f s i))
               (appl ( snd (sec (nB (ext f)))
                           (λ s → transport (λ i → B (isExt f s (~ i))) (ind nB g (f s))) ) s) i
  
  ind nB g (≡ext {x} {y} p i)
    = hcomp (λ k → λ { (i = i0) → transportRefl (ind nB g x) k
                     ; (i = i1) → transportRefl (ind nB g y) k })
            (fst (secCongDep' nB (≡ext p) (transport refl (ind nB g x)) (transport refl (ind nB g y)))
                 (λ i s → transport (λ j → B (≡isExt p s (~ j) i)) (ind nB g (p s i))) i)

  ind nB g (≡isExt {x} {y} p s j i)
    = hcomp (λ k → λ { (i = i0) → toPathP⁻-sq (ind nB g x) k j
                     ; (i = i1) → toPathP⁻-sq (ind nB g y) k j
                     ; (j = i1) → ind nB g (p s i) })
            (q₂ j i)
    
    where q₁ : Path (PathP (λ i → B (≡ext p i)) (transport refl (ind nB g x)) (transport refl (ind nB g y)))
                    (fst (secCongDep' nB (≡ext p) (transport refl (ind nB g x)) (transport refl (ind nB g y)))
                         (λ i s → transport (λ j → B (≡isExt p s (~ j) i)) (ind nB g (p s i))))
                    (λ i → transport (λ j → B (≡isExt p s (~ j) i)) (ind nB g (p s i)))
          q₁ j i = snd (secCongDep' nB (≡ext p) (transport refl (ind nB g x)) (transport refl (ind nB g y)))
                       (λ i s → transport (λ j → B (≡isExt p s (~ j) i)) (ind nB g (p s i))) j i s
          
          q₂ : PathP (λ j → PathP (λ i → B (≡isExt p s j i)) (toPathP⁻ (λ _ → B x) (λ _ → transport refl (ind nB g x)) j)
                                                             (toPathP⁻ (λ _ → B y) (λ _ → transport refl (ind nB g y)) j))
                     (fst (secCongDep' nB (≡ext p) (transport refl (ind nB g x)) (transport refl (ind nB g y)))
                        (λ i s → transport (λ j → B (≡isExt p s (~ j) i)) (ind nB g (p s i))))
                     (λ i → ind nB g (p s i))
          q₂ j i = toPathP⁻ (λ j → B (≡isExt p s j i)) (λ j → q₁ j i) j

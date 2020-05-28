{-# OPTIONS --cubical --safe #-}
module Cubical.Foundations.Path where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ

-- Less polymorphic version of `cong`, to avoid some unresolved metas
cong′ : ∀ {B : Type ℓ'} (f : A → B) {x y : A} (p : x ≡ y)
      → Path B (f x) (f y)
cong′ f = cong f
{-# INLINE cong′ #-}

PathP≡Path : ∀ (P : I → Type ℓ) (p : P i0) (q : P i1) →
             PathP P p q ≡ Path (P i1) (transport (λ i → P i) p) q
PathP≡Path P p q i = PathP (λ j → P (i ∨ j)) (transp (λ j → P (i ∧ j)) (~ i) p) q

PathP≃Path : ∀ (P : I → Type ℓ) (p : P i0) (q : P i1) →
             PathP P p q ≃ Path (P i1) (transport (λ i → P i) p) q
PathP≃Path P p q = transportEquiv (PathP≡Path P p q)

-- Alternative more unfolded proof
toPathP-isEquiv : ∀ (A : I → Set ℓ) {x y} → isEquiv (toPathP {A = A} {x} {y})
toPathP-isEquiv A {x} {y} = isoToIsEquiv (iso toPathP fromPathP to-from from-to)
 where
   to-from : ∀ (p : PathP A x y) → toPathP (fromPathP p) ≡ p
   to-from p h i = outS (hcomp-unique (λ { j (i = i0) → x ; j (i = i1) → fromPathP p j })
                                  (inS (transp (λ j → A (i ∧ j)) (~ i) x))
                                  \ h → inS (sq1 h i))
                        h
      where
        sq1 : (\ h → A [ x ≡ transp (\ j → A (h ∨ j)) h (p h) ]) [ (\ i → transp (λ j → A (i ∧ j)) (~ i) x) ≡ p ]
        sq1 = \ h i → comp (\ z → (hcomp (\ w →
                                                    \ { (z = i1) → A (i ∧ (w ∨ h))
                                                      ; (z = i0) → A (i ∧ h)
                                                      ; (i = i0) → A i0
                                                      ; (i = i1) → A (h ∨ (w ∧ z))
                                                      ; (h = i0) → A (i ∧ (w ∧ z))
                                                      ; (h = i1) → A i})
                                                   ((A (i ∧ h)))))
                                          (\ z → \ { (i = i0) → x
                                                   ; (i = i1) → transp (\ j → A (h ∨ (z ∧ j))) (h ∨ ~ z) (p h)
                                                   ; (h = i0) → transp (λ j → A ((i ∧ z) ∧ j)) (~ (i ∧ z)) x
                                                   ; (h = i1) → p i })
                                (p (i ∧ h))
   from-to : ∀ (q : transp A i0 x ≡ y) → fromPathP (toPathP {A = A} q) ≡ q
   from-to q = (\ h i → outS (transp-hcomp i {A' = A i1} (\ j → inS (A (i ∨ j)))
                                           ((λ { j (i = i0) → x ; j (i = i1) → q j }))
                                           (inS ((transp (λ j → A (i ∧ j)) (~ i) x))))
                             h)
             ∙ (\ h i → outS (hcomp-unique {A = A i1} ((λ { j (i = i0) → transp A i0 x ; j (i = i1) → q j }))
                                      (inS ((transp (λ j → A (i ∨ j)) i (transp (λ j → A (i ∧ j)) (~ i) x))))
                                      \ h → inS (sq2 h i))
                             h)
             ∙ sym (lUnit q)
     where
       sq2 : (\ h → transp A i0 x ≡ q h) [ (\ i → transp (\ j → A (i ∨ j)) i (transp (\ j → A (i ∧ j)) (~ i) x)) ≡ refl ∙ q ]
       sq2 = \ h i → comp (\ z → hcomp (\ w → \ { (i = i1) → A i1
                                              ; (i = i0) → A (h ∨ (w ∧ z))
                                              ; (h = i0) → A (i ∨ (w ∧ z))
                                              ; (h = i1) → A i1
                                              ; (z = i0) → A (i ∨ h)
                                              ; (z = i1) → A ((i ∨ h) ∨ w) })
                                             (A (i ∨ h)))
                 (\ z → \ { (i = i0) → transp (λ j → A ((z ∨ h) ∧ j)) (~ z ∧ ~ h) x
                          ; (i = i1) → q (z ∧ h)
                          ; (h = i1) → compPath-filler refl q z i
                          ; (h = i0) → transp (\ j → A (i ∨ (z ∧ j))) (i ∨ ~ z) (transp (\ j → A (i ∧ j)) (~ i) x)
                          })
                          (transp (\ j → A ((i ∨ h) ∧ j)) (~ (i ∨ h)) x)

PathP≡compPath : ∀ {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z) (r : x ≡ z)
                 → (PathP (λ i → x ≡ q i) p r) ≡ (p ∙ q ≡ r)
PathP≡compPath p q r k = PathP (λ i → p i0 ≡ q (i ∨ k)) (λ j → compPath-filler p q k j) r

PathP≡doubleCompPathˡ : ∀ {A : Type ℓ} {w x y z : A} (p : w ≡ y) (q : w ≡ x) (r : y ≡ z) (s : x ≡ z)
                        → (PathP (λ i → p i ≡ s i) q r) ≡ (p ⁻¹ ∙∙ q ∙∙ s ≡ r)
PathP≡doubleCompPathˡ p q r s k = PathP (λ i → p (i ∨ k) ≡ s (i ∨ k))
                                        (λ j → doubleCompPath-filler (p ⁻¹) q s k j) r

PathP≡doubleCompPathʳ : ∀ {A : Type ℓ} {w x y z : A} (p : w ≡ y) (q : w ≡ x) (r : y ≡ z) (s : x ≡ z)
                        → (PathP (λ i → p i ≡ s i) q r) ≡ (q ≡ p ∙∙ r ∙∙ s ⁻¹)
PathP≡doubleCompPathʳ p q r s k  = PathP (λ i → p (i ∧ (~ k)) ≡ s (i ∧ (~ k)))
                                         q (λ j → doubleCompPath-filler p r (s ⁻¹) k j)

compPathl-cancel : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : x ≡ z) → p ∙ (sym p ∙ q) ≡ q
compPathl-cancel p q = p ∙ (sym p ∙ q) ≡⟨ assoc p (sym p) q ⟩
                       (p ∙ sym p) ∙ q ≡⟨ cong (_∙ q) (rCancel p) ⟩
                              refl ∙ q ≡⟨ sym (lUnit q) ⟩
                                     q ∎

compPathr-cancel : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : z ≡ y) (q : x ≡ y) → (q ∙ sym p) ∙ p ≡ q
compPathr-cancel p q = (q ∙ sym p) ∙ p ≡⟨ sym (assoc q (sym p) p) ⟩
                       q ∙ (sym p ∙ p) ≡⟨ cong (q ∙_) (lCancel p) ⟩
                              q ∙ refl ≡⟨ sym (rUnit q) ⟩
                                     q ∎

compPathl-isEquiv : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y) → isEquiv (λ (q : y ≡ z) → p ∙ q)
compPathl-isEquiv p = isoToIsEquiv (iso (p ∙_) (sym p ∙_) (compPathl-cancel p) (compPathl-cancel (sym p)))

compPathr-isEquiv : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : y ≡ z) → isEquiv (λ (q : x ≡ y) → q ∙ p)
compPathr-isEquiv p = isoToIsEquiv (iso (_∙ p) (_∙ sym p) (compPathr-cancel p) (compPathr-cancel (sym p)))

-- Variation of isProp→isSet for PathP
isProp→isSet-PathP : ∀ {ℓ} {B : I → Type ℓ} → ((i : I) → isProp (B i))
                   → (b0 : B i0) (b1 : B i1)
                   → isProp (PathP (λ i → B i) b0 b1)
isProp→isSet-PathP {B = B} hB b0 b1 =
  transport (λ i → isProp (PathP≡Path B b0 b1 (~ i))) (isProp→isSet (hB i1) _ _)

-- Flipping a square along its diagonal

flipSquare : ∀ {ℓ} {A : Type ℓ}
  {a₀₀ a₀₁ : A} {a₀₋ : a₀₀ ≡ a₀₁}
  {a₁₀ a₁₁ : A} {a₁₋ : a₁₀ ≡ a₁₁}
  {a₋₀ : a₀₀ ≡ a₁₀} {a₋₁ : a₀₁ ≡ a₁₁}
  → Square a₀₋ a₁₋ a₋₀ a₋₁
  → Square a₋₀ a₋₁ a₀₋ a₁₋
flipSquare sq i j = sq j i

flipSquarePath : ∀ {ℓ} {A : Type ℓ}
  {a₀₀ a₀₁ : A} {a₀₋ : a₀₀ ≡ a₀₁}
  {a₁₀ a₁₁ : A} {a₁₋ : a₁₀ ≡ a₁₁}
  {a₋₀ : a₀₀ ≡ a₁₀} {a₋₁ : a₀₁ ≡ a₁₁}
  → Square a₀₋ a₁₋ a₋₀ a₋₁ ≡ Square a₋₀ a₋₁ a₀₋ a₁₋
flipSquarePath = isoToPath (iso flipSquare flipSquare (λ _ → refl) (λ _ → refl))

{-# OPTIONS --cubical --safe #-}
module Cubical.Foundations.Path where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Isomorphism

private
  variable
    ℓ ℓ' : Level
    A : Set ℓ

-- Less polymorphic version of `cong`, to avoid some unresolved metas
cong′ : ∀ {B : Set ℓ'} (f : A → B) {x y : A} (p : x ≡ y)
      → Path B (f x) (f y)
cong′ f = cong f



toPathP-isEquiv : ∀ (A : I → Set ℓ){x y} → isEquiv (toPathP {A = A} {x} {y})
toPathP-isEquiv A {x} {y}
  = isoToIsEquiv (iso toPathP fromPathP
    (\ { p k' i → outS
                   (hcomp-unique (λ { j (i = i0) → x ; j (i = i1) → fromPathP p j })
                    (inS (transp (λ j → A (i ∧ j)) (~ i) x))
                     \ h → inS (comp (\ z → (hcomp (\ w →
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
                                (inS (p (i ∧ h)))))
                    k' })
    \ q → (\ h i → outS (transp-hcomp i {A' = A i1} (\ j → inS (A (i ∨ j)))
                                        ((λ { j (i = i0) → x ; j (i = i1) → q j }))
                                        (inS ((transp (λ j → A (i ∧ j)) (~ i) x)))) h)
    ∙ (\ h i → outS (hcomp-unique {A = A i1} ((λ { j (i = i0) → transp A i0 x ; j (i = i1) → q j }))
                                  (inS ((transp (λ i₁ → A (i ∨ i₁)) i (transp (λ j → A (i ∧ j)) (~ i) x))))
       \ h → inS (comp (\ z → hcomp (\ w → \ { (i = i1) → A i1
                                             ; (i = i0) → A (h ∨ (w ∧ z))
                                             ; (h = i0) → A (i ∨ (w ∧ z))
                                             ; (h = i1) → A i1
                                             ; (z = i0) → A ( (i ∨ h) )
                                             ; (z = i1) → A ((i ∨ h) ∨ w) })
                                             ( (A (i ∨ h)) ))
                 (\ z → \ { (i = i0) → transp (λ j → A ((z ∨ h) ∧ j)) (~ z ∧ ~ h) x
                          ; (i = i1) → q (z ∧ h)
                          ; (h = i1) → compPath-filler refl q z i
                          ; (h = i0) → transp (\ j → A (i ∨ (z ∧ j))) (i ∨ ~ z) (transp (\ j → A (i ∧ j)) (~ i) x)
                          })
                          (inS (transp (\ j → A ((i ∨ h) ∧ j)) (~ (i ∨ h)) x)))
      )
      h) ∙ sym (lUnit q) )

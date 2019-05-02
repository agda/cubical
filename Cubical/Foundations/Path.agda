{-# OPTIONS --cubical --safe #-}
module Cubical.Foundations.Path where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Isomorphism

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ

-- Less polymorphic version of `cong`, to avoid some unresolved metas
cong′ : ∀ {B : Type ℓ'} (f : A → B) {x y : A} (p : x ≡ y)
      → Path B (f x) (f y)
cong′ f = cong f



toPathP-isEquiv : ∀ (A : I → Set ℓ){x y} → isEquiv (toPathP {A = A} {x} {y})
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
                                                   ((A (i ∧ h))))) _
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
                                             (A (i ∨ h))) _
                 (\ z → \ { (i = i0) → transp (λ j → A ((z ∨ h) ∧ j)) (~ z ∧ ~ h) x
                          ; (i = i1) → q (z ∧ h)
                          ; (h = i1) → compPath-filler refl q z i
                          ; (h = i0) → transp (\ j → A (i ∨ (z ∧ j))) (i ∨ ~ z) (transp (\ j → A (i ∧ j)) (~ i) x)
                          })
                          (transp (\ j → A ((i ∨ h) ∧ j)) (~ (i ∨ h)) x)

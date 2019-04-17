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
    \ q → (\ h i → outS (transp-hcomp i {A' = A i1} (\ j → inS (A (i ∨ j))) ((λ { j (i = i0) → x ; j (i = i1) → q j })) (inS ((transp (λ j → A (i ∧ j)) (~ i) x)))) h) ∙ (\ h i → outS (hcomp-cong ((λ { j (i = i0) → transp A i0 x ; j (i = i1) → q j })) (inS ((transp (λ i₁ → A (i ∨ i₁)) i (transp (λ j → A (i ∧ j)) (~ i) x)))) (((λ { j (i = i0) → transp A i0 x ; j (i = i1) → q j }))) (inS (transp A i0 x))
      (\ { j (i = i0) → refl; j (i = i1) → refl })
      (let r = compPathP' (transpFill {A = A i0} (~ i)  (λ j → inS (A (i ∧ j))) x)
                         (transpFill {A = A i1} i (\ j → inS (A (i ∨ j))) ((transp (λ j → A (i ∧ j)) (~ i) x))) \ k h → inS (A ((i ∨ h) ∧ k))  in
                           {!!})
      ) h) ∙ sym (lUnit q) )




-- (\ h i → hcomp (λ { j (i = i0) → transp A i0 x ; j (i = i1) → q j })
--         {!!})

-- let r = transp (\ j → A (j ∧ (i ∨ h))) (~ i ∧ ~ h) x in q i0


--    (transp (λ i₁ → A (i ∨ i₁)) i (transp (λ j → A (i ∧ j)) (~ i) x))



-- transp A i0 x                                                           transp A i0 x






--    transp  A i0 x
{-
(λ i →
   transp (λ j → A (i ∨ j)) i
   (hcomp (λ { j (i = i0) → x ; j (i = i1) → q j })
    (transp (λ j → A (i ∧ j)) (~ i) x)))
-}

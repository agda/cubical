{-# OPTIONS --cubical --postfix-projections #-}
module Cubical.Codata.M where

open import Cubical.Core.Prelude

-- TODO move
module Helpers where
  module _ {ℓ ℓ'} {A : Set ℓ} {x : A} (P : ∀ y → x ≡ y → Set ℓ') (d : P x refl) where
    -- A version with y as an explicit argument can be used to make Agda
    -- infer the family P.
    J' : ∀ y (p : x ≡ y) → P y p
    J' y p = J P d p

  lem-transp : {A : Set} (i : I) → (B : Set) (P : A ≡ B) → (p : P i) → PathP (\ j → P j) (transp (\ k → P (~ k ∧ i)) (~ i) p)
                                                                                         (transp (\ k → P (k ∨ i)) i p)
  lem-transp {A} i = J' _ (\ p j → transp (\ _ → A) ((~ j ∧ ~ i) ∨ (j ∧ i)) p )

  transp-over : (A : I → Set) (i j : I) → A i → A j
  transp-over A i k p = transp (\ j → A ((~ j ∧ i) ∨ (j ∧ k))) (~ i ∧ ~ k) p

  transp-over-1 : (A : I → Set) (i j : I) → A i → A j
  transp-over-1 A i k p = transp (\ j → A ((j ∨ i) ∧ (~ j ∨ k))) (i ∧ k) p

  compPathP : {ℓ ℓ' : _} {X : Set ℓ} (F : X → Set ℓ') {A B C : X} (P : A ≡ B) (Q : B ≡ C) (R : A ≡ C) → compPath P Q ≡ R
              → ∀ {x y z} → (\ i → F (P i)) [ x ≡ y ] → (\ i → F (Q i)) [ y ≡ z ] → (\ i → F (R i)) [ x ≡ z ]
  compPathP F {A = A} P Q = J' _ \ {x} p q i → comp (\ j → F (hfill (λ j → \ { (i = i0) → A
                 ; (i = i1) → Q j }) (inc (P i)) j)) (λ j → \ { (i = i0) → x; (i = i1) → q j }) (inc (p i))

open Helpers

IxCont : Set → Set₁
IxCont X = Σ (X → Set) \ S → ∀ x → S x → X → Set


⟦_⟧ : ∀ {X : Set} → IxCont X → (X → Set) → (X → Set)
⟦ (S , P) ⟧ X x = Σ (S x) \ s → ∀ y → P x s y → X y


record M {X : Set} (C : IxCont X) (x : X) : Set where
  coinductive
  field
    head : C .fst x
    tails : ∀ y → C .snd x head y → M C y

open M public

module _ {X : Set} {C : IxCont X} where

  private
    F = ⟦ C ⟧

  out : ∀ x → M C x → F (M C) x
  out x a = (a .head) , (a .tails)

  mapF : ∀ {A B} → (∀ x → A x → B x) → ∀ x → F A x → F B x
  mapF f x (s , t) = s , \ y p → f _ (t y p)

  unfold : ∀ {A} (α : ∀ x → A x → F A x) → ∀ x → A x → M C x
  unfold α x a .head = α x a .fst
  unfold α x a .tails y p = unfold α y (α x a .snd y p)


  unfold-η' : ∀ {A} (α : ∀ x → A x → F A x) → (h : ∀ x → A x → M C x)
                     → (∀ (x : X) (a : A x) → out x (h x a) ≡ mapF h x (α x a))
                     → ∀ (x : X) (a : A x) m → h x a ≡ m → m ≡ unfold α x a
  unfold-η' α h eq x a m eq' = let heq = compPath (cong head (sym eq')) (cong fst (eq x a))
                               in \ where
                                    i .head → heq i
                                    i .tails y p →
                                     let  p0 = (transp-over-1 (\ k → C .snd x (heq k) y) i i1 p)
                                          p1 = (transp-over (\ k → C .snd x (heq k) y) i i0 p)
                                          pe = lem-transp i _ (\ k → C .snd x (heq k) y) p
                                          tl = compPathP (λ p → C .snd x p y → M C y)
                                                         (cong head (sym eq')) (cong fst (eq x a)) heq
                                                         refl
                                                         (cong (\ f → f .tails y) (sym eq'))
                                                         (cong (\ f → f .snd   y) (eq x a))
                                     in unfold-η' α h eq y (α x a .snd y p0)
                                                           (m .tails y p1)
                                                           (sym (\ k → tl k (pe k)))
                                                           i

  unfold-η : ∀ {A} (α : ∀ x → A x → F A x) → (h : ∀ x → A x → M C x)
                     → (∀ (x : X) (a : A x) → out x (h x a) ≡ mapF h x (α x a))
                     → ∀ (x : X) (a : A x) → h x a ≡ unfold α x a
  unfold-η α h eq x a = unfold-η' α h eq x a _ refl

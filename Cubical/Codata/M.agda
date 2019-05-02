{-# OPTIONS --cubical --safe --guardedness #-}
module Cubical.Codata.M where

open import Cubical.Foundations.Prelude

-- TODO move
module Helpers where
  module _ {ℓ ℓ'} {A : Type ℓ} {x : A} (P : ∀ y → x ≡ y → Type ℓ') (d : P x refl) where
    -- A version with y as an explicit argument can be used to make Agda
    -- infer the family P.
    J' : ∀ y (p : x ≡ y) → P y p
    J' y p = J P d p

  lem-transp : ∀ {ℓ} {A : Type ℓ} (i : I) → (B : Type ℓ) (P : A ≡ B) → (p : P i) → PathP (\ j → P j) (transp (\ k → P (~ k ∧ i)) (~ i) p)
                                                                                         (transp (\ k → P (k ∨ i)) i p)
  lem-transp {A = A} i = J' _ (\ p j → transp (\ _ → A) ((~ j ∧ ~ i) ∨ (j ∧ i)) p )

  transp-over : ∀ {ℓ} (A : I → Type ℓ) (i j : I) → A i → A j
  transp-over A i k p = transp (\ j → A ((~ j ∧ i) ∨ (j ∧ k))) (~ i ∧ ~ k) p

  transp-over-1 : ∀ {ℓ} (A : I → Type ℓ) (i j : I) → A i → A j
  transp-over-1 A i k p = transp (\ j → A ((j ∨ i) ∧ (~ j ∨ k))) (i ∧ k) p

  compPathD : {ℓ ℓ' : _} {X : Type ℓ} (F : X → Type ℓ') {A B C : X} (P : A ≡ B) (Q : B ≡ C)
              → ∀ {x y z} → (\ i → F (P i)) [ x ≡ y ] → (\ i → F (Q i)) [ y ≡ z ] → (\ i → F ((P ∙ Q) i)) [ x ≡ z ]
  compPathD F {A = A} P Q {x} p q i =
     comp (\ j → F (hfill (λ j → \ { (i = i0) → A ; (i = i1) → Q j })
                          (inS (P i))
                          j)) _
          (λ j → \ { (i = i0) → x; (i = i1) → q j })
          (p i)

open Helpers

IxCont : Type₀ → Type₁
IxCont X = Σ (X → Type₀) \ S → ∀ x → S x → X → Type₀


⟦_⟧ : ∀ {X : Type₀} → IxCont X → (X → Type₀) → (X → Type₀)
⟦ (S , P) ⟧ X x = Σ (S x) \ s → ∀ y → P x s y → X y


record M {X : Type₀} (C : IxCont X) (x : X) : Type₀ where
  coinductive
  field
    head : C .fst x
    tails : ∀ y → C .snd x head y → M C y

open M public

module _ {X : Type₀} {C : IxCont X} where

  private
    F = ⟦ C ⟧

  out : ∀ x → M C x → F (M C) x
  out x a = (a .head) , (a .tails)

  mapF : ∀ {A B} → (∀ x → A x → B x) → ∀ x → F A x → F B x
  mapF f x (s , t) = s , \ y p → f _ (t y p)

  unfold : ∀ {A} (α : ∀ x → A x → F A x) → ∀ x → A x → M C x
  unfold α x a .head = α x a .fst
  unfold α x a .tails y p = unfold α y (α x a .snd y p)


  -- We generalize the type to avoid upsetting --guardedness by
  -- transporting after the corecursive call.
  -- Recognizing hcomp/transp as guardedness-preserving could be a better solution.
  unfold-η' : ∀ {A} (α : ∀ x → A x → F A x) → (h : ∀ x → A x → M C x)
                     → (∀ (x : X) (a : A x) → out x (h x a) ≡ mapF h x (α x a))
                     → ∀ (x : X) (a : A x) m → h x a ≡ m → m ≡ unfold α x a
  unfold-η' α h eq x a m eq' = let heq = cong head (sym eq') ∙ cong fst (eq x a)
                               in \ where
                                    i .head → heq i
                                    i .tails y p →
                                     let  p0 = (transp-over-1 (\ k → C .snd x (heq k) y) i i1 p)
                                          p1 = (transp-over (\ k → C .snd x (heq k) y) i i0 p)
                                          pe = lem-transp i _ (\ k → C .snd x (heq k) y) p
                                          tl = compPathD (λ p → C .snd x p y → M C y)
                                                         (cong head (sym eq')) (cong fst (eq x a))
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

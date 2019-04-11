{-

Half adjoint equivalences ([HAEquiv])

- Iso to HAEquiv ([iso→HAEquiv])
- Equiv to HAEquiv ([equiv→HAEquiv])
- Cong is an equivalence ([congEquiv])

-}
{-# OPTIONS --cubical --safe #-}
module Cubical.Foundations.HAEquiv where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Data.Nat

record isHAEquiv {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B) : Type (ℓ-max ℓ ℓ') where
  field
    g : B → A
    sec : ∀ a → g (f a) ≡ a
    ret : ∀ b → f (g b) ≡ b
    com : ∀ a → cong f (sec a) ≡ ret (f a)

HAEquiv : ∀ {ℓ ℓ'} (A : Type ℓ) (B : Type ℓ') → Type (ℓ-max ℓ ℓ')
HAEquiv A B = Σ (A → B) λ f → isHAEquiv f

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    B : Type ℓ'

iso→HAEquiv : Iso A B → HAEquiv A B
iso→HAEquiv {A = A} {B = B} (iso f g ε η) = f , (record { g = g ; sec = η ; ret = ret ; com = com })
  where
    sides : ∀ b i j → Partial (~ i ∨ i) B
    sides b i j = λ { (i = i0) → ε (f (g b)) j
                    ; (i = i1) → ε b j }

    bot : ∀ b i → B
    bot b i = cong f (η (g b)) i

    ret : (b : B) → f (g b) ≡ b
    ret b i = hcomp (sides b i) (bot b i)

    com : (a : A) → cong f (η a) ≡ ret (f a)
    com a i j = hcomp (λ k → λ { (i = i0) → ε (f (η a j)) k
                               ; (i = i1) → hfill (sides (f a) j) (inS (bot (f a) j)) k
                               ; (j = i0) → ε (f (g (f a))) k
                               ; (j = i1) → ε (f a) k})
                      (cong (cong f) (sym (Hfa≡fHa (λ x → g (f x)) η a)) i j)

equiv→HAEquiv : A ≃ B → HAEquiv A B
equiv→HAEquiv e = iso→HAEquiv (equivToIso e)

congEquiv : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {x y : A} (e : A ≃ B) → (x ≡ y) ≃ (e .fst x ≡ e .fst y)
congEquiv {A = A} {B} {x} {y} e = isoToEquiv (iso intro elim intro-elim elim-intro)
  where
    e' : HAEquiv A B
    e' = equiv→HAEquiv e

    f : A → B
    f = e' .fst

    g : B → A
    g = isHAEquiv.g (e' .snd)

    sec : ∀ a → g (f a) ≡ a
    sec = isHAEquiv.sec (e' .snd)

    ret : ∀ b → f (g b) ≡ b
    ret = isHAEquiv.ret (e' .snd)

    com : ∀ a → cong f (sec a) ≡ ret (f a)
    com = isHAEquiv.com (e' .snd)

    intro : x ≡ y → f x ≡ f y
    intro = cong f

    elim-sides : ∀ p i j → Partial (~ i ∨ i) A
    elim-sides p i j = λ { (i = i0) → sec x j
                         ; (i = i1) → sec y j }

    elim-bot : ∀ p i → A
    elim-bot p i = cong g p i

    elim : f x ≡ f y → x ≡ y
    elim p i = hcomp (elim-sides p i) (elim-bot p i)

    intro-elim : ∀ p → intro (elim p) ≡ p
    intro-elim p i j =
      hcomp (λ k → λ { (i = i0) → f (hfill (elim-sides p j)
                                    (inS (elim-bot p j)) k)
                     ; (i = i1) → ret (p j) k
                     ; (j = i0) → com x i k
                     ; (j = i1) → com y i k })
            (f (g (p j)))

    elim-intro : ∀ p → elim (intro p) ≡ p
    elim-intro p i j =
      hcomp (λ k → λ { (i = i0) → hfill (λ l → λ { (j = i0) → secEq e x l
                                                 ; (j = i1) → secEq e y l })
                                        (inS (cong (λ z → g (f z)) p j)) k
                     ; (i = i1) → p j
                     ; (j = i0) → secEq e x (i ∨ k)
                     ; (j = i1) → secEq e y (i ∨ k) })
            (secEq e (p j) i)

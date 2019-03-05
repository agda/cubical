{-# OPTIONS --cubical --safe #-}
module Cubical.Foundations.HAEquiv where

open import Agda.Primitive
open import Cubical.Core.Prelude
open import Cubical.Core.Glue
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence

record isHAEquiv {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) : Set (ℓ ⊔ ℓ') where
  field
    g : B → A
    sec : ∀ a → g (f a) ≡ a
    ret : ∀ b → f (g b) ≡ b
    com : ∀ a → cong f (sec a) ≡ ret (f a)

HAEquiv : ∀ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') → Set (ℓ ⊔ ℓ')
HAEquiv A B = Σ (A → B) λ f → isHAEquiv f

private
  variable
    ℓ ℓ' : Level
    A : Set ℓ
    B : Set ℓ'

homotopyNatural' : {f g : A → B} (H : ∀ a → f a ≡ g a) {x y : A} (p : x ≡ y) → compPath (H x) (cong g p) ≡ compPath' (cong f p) (H y)
homotopyNatural' {f = f} {g = g} H {x} {y} p i j =
  hcomp (λ k → \ { (i = i0) → hfill (compPath-sides (H x) (cong g p) j)
                                    (inc (compPath-bot (H x) (cong g p) j)) k
                 ; (i = i1) → hfill (compPath'-sides (cong f p) (H y) j)
                                    (inc (compPath'-bot (cong f p) (H y) j)) k
                 ; (j = i0) → cong f p (i ∧ (~ k))
                 ; (j = i1) → cong g p (i ∨ k) })
        (H (p i) j)

homotopyNatural : {f g : A → B} (H : ∀ a → f a ≡ g a) {x y : A} (p : x ≡ y) → compPath (H x) (cong g p) ≡ compPath (cong f p) (H y)
homotopyNatural H p = compPath (homotopyNatural' H p) (sym (compPath≡compPath' _ _))

Hfa≡fHa : ∀ {ℓ} {A : Set ℓ} (f : A → A) (H : ∀ a → f a ≡ a) → ∀ a → H (f a) ≡ cong f (H a)
Hfa≡fHa {A = A} f H a = H (f a) ≡⟨ sym (rUnit (H (f a))) ⟩
                        compPath (H (f a)) refl ≡⟨ cong (compPath (H (f a))) (sym (rInv (H a))) ⟩
                        compPath (H (f a)) (compPath (H a) (sym (H a))) ≡⟨ sym (compPath-assoc _ _ _ )⟩
                        compPath (compPath (H (f a)) (H a)) (sym (H a)) ≡⟨ cong (λ x → compPath x (sym (H a))) (homotopyNatural H (H a)) ⟩
                        compPath (compPath (cong f (H a)) (H a)) (sym (H a)) ≡⟨ compPath-assoc _ _ _ ⟩
                        compPath (cong f (H a)) (compPath (H a) (sym (H a))) ≡⟨ cong (compPath (cong f (H a))) (rInv _) ⟩
                        compPath (cong f (H a)) refl ≡⟨ rUnit _ ⟩
                        cong f (H a) ∎

iso→HAEquiv : Iso A B → HAEquiv A B
iso→HAEquiv {A = A} {B = B} (iso f g ε η) = f , (record { g = g ; sec = η ; ret = ret ; com = com })
  where
    sides : ∀ b i j → Partial (~ i ∨ i) B
    sides b i j = \ { (i = i0) → ε (f (g b)) j
                   ; (i = i1) → ε b j }

    bot : ∀ b i → B
    bot b i = cong f (η (g b)) i

    ret : (b : B) → f (g b) ≡ b
    ret b i = hcomp (sides b i) (bot b i)

    com : (a : A) → cong f (η a) ≡ ret (f a)
    com a i j = hcomp (λ k → \ { (i = i0) → ε (f (η a j)) k
                                ; (i = i1) → hfill (sides (f a) j) (inc (bot (f a) j)) k
                                ; (j = i0) → ε (f (g (f a))) k
                                ; (j = i1) → ε (f a) k})
                       ( cong (cong f) (sym (Hfa≡fHa (λ x → g (f x)) η a)) i j)

equiv→HAEquiv : A ≃ B → HAEquiv A B
equiv→HAEquiv e = iso→HAEquiv (equivToIso e)

congEquiv : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {x y : A} (e : A ≃ B) → (x ≡ y) ≃ (e .fst x ≡ e .fst y)
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
    elim-sides p i j = \ { (i = i0) → sec x j
                     ; (i = i1) → sec y j
                     }

    elim-bot : ∀ p i → A
    elim-bot p i = cong g p i

    elim : f x ≡ f y → x ≡ y
    elim p i = hcomp (elim-sides p i) (elim-bot p i)

    intro-elim : ∀ p → intro (elim p) ≡ p
    intro-elim p i j = hcomp (λ k → \ { (i = i0) → f (hfill (elim-sides p j)
                                                             (inc (elim-bot p j)) k)
                                       ; (i = i1) → ret (p j) k
                                       ; (j = i0) → com x i k
                                       ; (j = i1) → com y i k })
                              (f (g (p j)))

    elim-intro : ∀ p → elim (intro p) ≡ p
    elim-intro p i j = hcomp (λ k → \ { (i = i0) → hfill (λ l → λ { (j = i0) → secEq e x l ; (j = i1) → secEq e y l })
                                                     (inc (cong (λ z → g (f z)) p j)) k
                                       ; (i = i1) → p j
                                       ; (j = i0) → secEq e x (i ∨ k)
                                       ; (j = i1) → secEq e y (i ∨ k)
                                      }) (secEq e (p j) i)

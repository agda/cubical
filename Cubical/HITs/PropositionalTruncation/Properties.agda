{-

This file contains:

- Eliminator for propositional truncation

-}
{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.PropositionalTruncation.Properties where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.HITs.PropositionalTruncation.Base

private
  variable
    ℓ : Level
    A B : Type ℓ

recPropTrunc : ∀ {P : Type ℓ} → isProp P → (A → P) → ∥ A ∥ → P
recPropTrunc Pprop f ∣ x ∣          = f x
recPropTrunc Pprop f (squash x y i) =
  Pprop (recPropTrunc Pprop f x) (recPropTrunc Pprop f y) i

propTruncIsProp : isProp ∥ A ∥
propTruncIsProp x y = squash x y

elimPropTrunc : ∀ {P : ∥ A ∥ → Type ℓ} → ((a : ∥ A ∥) → isProp (P a)) →
                ((x : A) → P ∣ x ∣) → (a : ∥ A ∥) → P a
elimPropTrunc                 Pprop f ∣ x ∣          = f x
elimPropTrunc {A = A} {P = P} Pprop f (squash x y i) =
  PpropOver (squash x y) (elimPropTrunc Pprop f x) (elimPropTrunc Pprop f y) i
    where
    PpropOver : {a b : ∥ A ∥} → (sq : a ≡ b) → ∀ x y → PathP (λ i → P (sq i)) x y
    PpropOver {a} = J (λ b (sq : a ≡ b) → ∀ x y → PathP (λ i → P (sq i)) x y) (Pprop a)

-- We could also define the eliminator using the recursor
elimPropTrunc' : ∀ {P : ∥ A ∥ → Type ℓ} → ((a : ∥ A ∥) → isProp (P a)) →
                 ((x : A) → P ∣ x ∣) → (a : ∥ A ∥) → P a
elimPropTrunc' {P = P} Pprop f a =
  recPropTrunc (Pprop a) (λ x → transp (λ i → P (squash ∣ x ∣ a i)) i0 (f x)) a

module SetElim (Bset : isSet B) where
  Bset' : isSet' B
  Bset' = isSet→isSet' Bset

  recPropTrunc→Set : (f : A → B) (kf : 2-Constant f) → ∥ A ∥ → B
  helper
    : (f : A → B) (kf : 2-Constant f) → (t u : ∥ A ∥)
    → recPropTrunc→Set f kf t ≡ recPropTrunc→Set f kf u

  recPropTrunc→Set f kf ∣ x ∣ = f x
  recPropTrunc→Set f kf (squash t u i) = helper f kf t u i

  helper f kf ∣ x ∣ ∣ y ∣ = kf x y
  helper f kf (squash t u i) v
    = Bset' (helper f kf t v) (helper f kf u v) (helper f kf t u) refl i
  helper f kf t (squash u v i)
    = Bset' (helper f kf t u) (helper f kf t v) refl (helper f kf u v) i

  kcomp : ∀(f : ∥ A ∥ → B) → 2-Constant (f ∘ ∣_∣)
  kcomp f x y = cong f (squash ∣ x ∣ ∣ y ∣)

  Fset : isSet (A → B)
  Fset = isSetPi (const Bset)

  Kset : (f : A → B) → isSet (2-Constant f)
  Kset f = isSetPi (λ _ → isSetPi (λ _ → isProp→isSet (Bset _ _)))

  setRecLemma
    : (Bset : isSet B)
    → (f : ∥ A ∥ → B)
    → recPropTrunc→Set (f ∘ ∣_∣) (kcomp f) ≡ f
  setRecLemma Bset f i t
    = elimPropTrunc {P = λ t → recPropTrunc→Set (f ∘ ∣_∣) (kcomp f) t ≡ f t}
        (λ t → Bset _ _) (λ x → refl) t i

  mkKmap : (∥ A ∥ → B) → Σ (A → B) 2-Constant
  mkKmap f = f ∘ ∣_∣ , kcomp f

  fib : (g : Σ (A → B) 2-Constant) → fiber mkKmap g
  fib (g , kg) = recPropTrunc→Set g kg , refl

  eqv : (g : Σ (A → B) 2-Constant)
      → ∀ fi → fib g ≡ fi
  eqv g (f , p) =
    ΣProp≡ (λ f → isOfHLevelΣ 2 Fset Kset _ _)
      (cong (uncurry recPropTrunc→Set) (sym p) ∙ setRecLemma Bset f)

  trunc→Set≃ : (∥ A ∥ → B) ≃ (Σ (A → B) 2-Constant)
  trunc→Set≃ .fst = mkKmap
  trunc→Set≃ .snd .equiv-proof g = fib g , eqv g

open SetElim public using (recPropTrunc→Set; trunc→Set≃)

RecHProp : (P : A → hProp {ℓ}) (kP : ∀ x y → P x ≡ P y) → ∥ A ∥ → hProp {ℓ}
RecHProp P kP = recPropTrunc→Set isSetHProp P kP

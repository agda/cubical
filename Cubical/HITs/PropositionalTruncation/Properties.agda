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

module GpdElim
  (Bgpd : isGroupoid B)
  (f : A → B)
  (3kf : 3-Constant f)
  where
  kf : 2-Constant f
  kf = fst 3kf

  coh₁ : ∀ x y z → Square refl (kf x y) (kf x z) (kf y z)
  coh₁ = snd 3kf

  Bgpd₂ : isGroupoid₂ B
  Bgpd₂ = isGroupoid₁→isGroupoid₂ (isGroupoid→isGroupoid₁ Bgpd)

  coh₂ : ∀ x y z → Square (kf x y) (kf x z) (kf y z) refl
  coh₂ x y z i j
    = hcomp (λ k → λ
        { (j = i0) → kf x y i
        ; (i = i0) → kf x z (j ∧ k)
        ; (j = i1) → kf x z (i ∨ k)
        ; (i = i1) → kf y z j
        })
        (coh₁ x y z j i)

  recPropTrunc→Gpd : ∥ A ∥ → B
  pathHelper : (t u : ∥ A ∥) → recPropTrunc→Gpd t ≡ recPropTrunc→Gpd u
  triHelper₁
    : (t u v : ∥ A ∥)
    → Square refl (pathHelper t u) (pathHelper t v) (pathHelper u v)
  triHelper₂
    : (t u v : ∥ A ∥)
    → Square (pathHelper t u) (pathHelper t v) (pathHelper u v) refl

  recPropTrunc→Gpd ∣ x ∣ = f x
  recPropTrunc→Gpd (squash t u i) = pathHelper t u i

  pathHelper ∣ x ∣ ∣ y ∣ = kf x y
  pathHelper (squash t u j) v = triHelper₂ t u v j
  pathHelper ∣ x ∣ (squash u v j) = triHelper₁ ∣ x ∣ u v j

  triHelper₁ ∣ x ∣ ∣ y ∣ ∣ z ∣ = coh₁ x y z
  triHelper₁ (squash s t i) u v
    = Bgpd₂
        (λ i → refl)
        (triHelper₂ s t u)
        (triHelper₂ s t v)
        (λ i → pathHelper u v)
        (triHelper₁ s u v)
        (triHelper₁ t u v) i
  triHelper₁ ∣ x ∣ (squash t u i) v
    = Bgpd₂
        (λ i → refl)
        (triHelper₁ ∣ x ∣ t u)
        (λ i → pathHelper ∣ x ∣ v)
        (triHelper₂ t u v)
        (triHelper₁ ∣ x ∣ t v)
        (triHelper₁ ∣ x ∣ u v)
        i
  triHelper₁ ∣ x ∣ ∣ y ∣ (squash u v i)
    = Bgpd₂
        (λ i → refl)
        (λ i → kf x y)
        (triHelper₁ ∣ x ∣ u v)
        (triHelper₁ ∣ y ∣ u v)
        (triHelper₁ ∣ x ∣ ∣ y ∣ u)
        (triHelper₁ ∣ x ∣ ∣ y ∣ v)
        i

  triHelper₂ ∣ x ∣ ∣ y ∣ ∣ z ∣ = coh₂ x y z
  triHelper₂ (squash s t i) u v
    = Bgpd₂
        (triHelper₂ s t u)
        (triHelper₂ s t v)
        (λ i → pathHelper u v)
        (λ i → refl)
        (triHelper₂ s u v)
        (triHelper₂ t u v)
        i
  triHelper₂ ∣ x ∣ (squash t u i) v
    = Bgpd₂
        (triHelper₁ ∣ x ∣ t u)
        (λ i → pathHelper ∣ x ∣ v)
        (triHelper₂ t u v)
        (λ i → refl)
        (triHelper₂ ∣ x ∣ t v)
        (triHelper₂ ∣ x ∣ u v)
        i
  triHelper₂ ∣ x ∣ ∣ y ∣ (squash u v i)
    = Bgpd₂
        (λ i → kf x y)
        (triHelper₁ ∣ x ∣ u v)
        (triHelper₁ ∣ y ∣ u v)
        (λ i → refl)
        (triHelper₂ ∣ x ∣ ∣ y ∣ u)
        (triHelper₂ ∣ x ∣ ∣ y ∣ v)
        i

open GpdElim using (recPropTrunc→Gpd) public

RecHSet : (P : A → HLevel {ℓ} 2) → 3-Constant P → ∥ A ∥ → HLevel {ℓ} 2
RecHSet P 3kP = recPropTrunc→Gpd (hLevelHLevelSuc 1) P 3kP

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
open import Cubical.Foundations.Isomorphism

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

-- The propositional truncation can be eliminated into non-propositional
-- types as long as the function used in the eliminator is 'coherently
-- constant.' The details of this can be found in the following paper:
--
--   https://arxiv.org/pdf/1411.2682.pdf
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
    : (f : ∥ A ∥ → B)
    → recPropTrunc→Set (f ∘ ∣_∣) (kcomp f) ≡ f
  setRecLemma f i t
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
      (cong (uncurry recPropTrunc→Set) (sym p) ∙ setRecLemma f)

  trunc→Set≃ : (∥ A ∥ → B) ≃ (Σ (A → B) 2-Constant)
  trunc→Set≃ .fst = mkKmap
  trunc→Set≃ .snd .equiv-proof g = fib g , eqv g

  -- The strategy of this equivalence proof follows the paper more closely.
  -- It is used further down for the groupoid version, because the above
  -- strategy does not generalize so easily.
  e : B → Σ (A → B) 2-Constant
  e b = const b , λ _ _ → refl

  eval : A → (γ : Σ (A → B) 2-Constant) → B
  eval a₀ (g , _) = g a₀

  e-eval : ∀ (a₀ : A) γ → e (eval a₀ γ) ≡ γ
  e-eval a₀ (g , kg) i .fst a₁ = kg a₀ a₁ i
  e-eval a₀ (g , kg) i .snd a₁ a₂ = Bset' refl (kg a₁ a₂) (kg a₀ a₁) (kg a₀ a₂) i

  e-isEquiv : A → isEquiv (e {A = A})
  e-isEquiv a₀ = isoToIsEquiv (iso e (eval a₀) (e-eval a₀) λ _ → refl)

  preEquiv₁ : ∥ A ∥ → B ≃ Σ (A → B) 2-Constant
  preEquiv₁ t = e , recPropTrunc (isPropIsEquiv e) e-isEquiv t

  preEquiv₂ : (∥ A ∥ → Σ (A → B) 2-Constant) ≃ Σ (A → B) 2-Constant
  preEquiv₂ = isoToEquiv (iso to const (λ _ → refl) retr)
    where
    to : (∥ A ∥ → Σ (A → B) 2-Constant) → Σ (A → B) 2-Constant
    to f .fst x = f ∣ x ∣ .fst x
    to f .snd x y i = f (squash ∣ x ∣ ∣ y ∣ i) .snd x y i

    retr : retract to const
    retr f i t .fst x = f (squash ∣ x ∣ t i) .fst x
    retr f i t .snd x y
      = Bset'
          (λ j → f (squash ∣ x ∣ ∣ y ∣ j) .snd x y j)
          (f t .snd x y)
          (λ j → f (squash ∣ x ∣ t j) .fst x)
          (λ j → f (squash ∣ y ∣ t j) .fst y)
          i

  trunc→Set≃₂ : (∥ A ∥ → B) ≃ Σ (A → B) 2-Constant
  trunc→Set≃₂ = compEquiv (equivPi preEquiv₁) preEquiv₂

open SetElim public using (recPropTrunc→Set; trunc→Set≃)

elimPropTrunc→Set
  : {P : ∥ A ∥ → Set ℓ}
  → (∀ t → isSet (P t))
  → (f : (x : A) → P ∣ x ∣)
  → (kf : ∀ x y → PathP (λ i → P (squash ∣ x ∣ ∣ y ∣ i)) (f x) (f y))
  → (t : ∥ A ∥) → P t
elimPropTrunc→Set {A = A} {P = P} Pset f kf t
  = recPropTrunc→Set (Pset t) g gk t
  where
  g : A → P t
  g x = transp (λ i → P (squash ∣ x ∣ t i)) i0 (f x)

  gk : 2-Constant g
  gk x y i = transp (λ j → P (squash (squash ∣ x ∣ ∣ y ∣ i) t j)) i0 (kf x y i)

RecHProp : (P : A → hProp ℓ) (kP : ∀ x y → P x ≡ P y) → ∥ A ∥ → hProp ℓ
RecHProp P kP = recPropTrunc→Set isSetHProp P kP

module GpdElim (Bgpd : isGroupoid B) where
  Bgpd' : isGroupoid' B
  Bgpd' = isGroupoid→isGroupoid' Bgpd

  module _ (f : A → B) (3kf : 3-Constant f) where
    open 3-Constant 3kf

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

    pathHelper ∣ x ∣ ∣ y ∣ = link x y
    pathHelper (squash t u j) v = triHelper₂ t u v j
    pathHelper ∣ x ∣ (squash u v j) = triHelper₁ ∣ x ∣ u v j

    triHelper₁ ∣ x ∣ ∣ y ∣ ∣ z ∣ = coh₁ x y z
    triHelper₁ (squash s t i) u v
      = Bgpd'
          (λ i → refl)
          (triHelper₂ s t u)
          (triHelper₂ s t v)
          (λ i → pathHelper u v)
          (triHelper₁ s u v)
          (triHelper₁ t u v) i
    triHelper₁ ∣ x ∣ (squash t u i) v
      = Bgpd'
          (λ i → refl)
          (triHelper₁ ∣ x ∣ t u)
          (λ i → pathHelper ∣ x ∣ v)
          (triHelper₂ t u v)
          (triHelper₁ ∣ x ∣ t v)
          (triHelper₁ ∣ x ∣ u v)
          i
    triHelper₁ ∣ x ∣ ∣ y ∣ (squash u v i)
      = Bgpd'
          (λ i → refl)
          (λ i → link x y)
          (triHelper₁ ∣ x ∣ u v)
          (triHelper₁ ∣ y ∣ u v)
          (triHelper₁ ∣ x ∣ ∣ y ∣ u)
          (triHelper₁ ∣ x ∣ ∣ y ∣ v)
          i

    triHelper₂ ∣ x ∣ ∣ y ∣ ∣ z ∣ = coh₂ x y z
    triHelper₂ (squash s t i) u v
      = Bgpd'
          (triHelper₂ s t u)
          (triHelper₂ s t v)
          (λ i → pathHelper u v)
          (λ i → refl)
          (triHelper₂ s u v)
          (triHelper₂ t u v)
          i
    triHelper₂ ∣ x ∣ (squash t u i) v
      = Bgpd'
          (triHelper₁ ∣ x ∣ t u)
          (λ i → pathHelper ∣ x ∣ v)
          (triHelper₂ t u v)
          (λ i → refl)
          (triHelper₂ ∣ x ∣ t v)
          (triHelper₂ ∣ x ∣ u v)
          i
    triHelper₂ ∣ x ∣ ∣ y ∣ (squash u v i)
      = Bgpd'
          (λ i → link x y)
          (triHelper₁ ∣ x ∣ u v)
          (triHelper₁ ∣ y ∣ u v)
          (λ i → refl)
          (triHelper₂ ∣ x ∣ ∣ y ∣ u)
          (triHelper₂ ∣ x ∣ ∣ y ∣ v)
          i

  preEquiv₁ : (∥ A ∥ → Σ (A → B) 3-Constant) ≃ Σ (A → B) 3-Constant
  preEquiv₁ = isoToEquiv (iso fn const (λ _ → refl) retr)
    where
    open 3-Constant

    fn : (∥ A ∥ → Σ (A → B) 3-Constant) → Σ (A → B) 3-Constant
    fn f .fst x = f ∣ x ∣ .fst x
    fn f .snd .link x y i = f (squash ∣ x ∣ ∣ y ∣ i) .snd .link x y i
    fn f .snd .coh₁ x y z i j
      = f (squash ∣ x ∣ (squash ∣ y ∣ ∣ z ∣ i) j) .snd .coh₁ x y z i j

    retr : retract fn const
    retr f i t .fst x = f (squash ∣ x ∣ t i) .fst x
    retr f i t .snd .link x y j
      = f (squash (squash ∣ x ∣ ∣ y ∣ j) t i) .snd .link x y j
    retr f i t .snd .coh₁ x y z
      = Bgpd'
          (λ _ → refl)
          (λ k j → f (cb i0 j k) .snd .link x y j)
          (λ k j → f (cb i1 j k) .snd .link x z j)
          (λ k j → f (cb j i1 k) .snd .link y z j)
          (λ k j → f (cb k j i0) .snd .coh₁ x y z k j )
          (λ k j → f (cb k j i1) .snd .coh₁ x y z k j)
          i
      where
      cb : I → I → I → ∥ _ ∥
      cb i j k = squash (squash ∣ x ∣ (squash ∣ y ∣ ∣ z ∣ i) j) t k

  e : B → Σ (A → B) 3-Constant
  e b .fst _ = b
  e b .snd = record
           { link = λ _ _ _ → b
           ; coh₁ = λ _ _ _ _ _ → b
           }

  eval : A → Σ (A → B) 3-Constant → B
  eval a₀ (g , _) = g a₀

  module _ where
    open 3-Constant
    e-eval : ∀(a₀ : A) γ → e (eval a₀ γ) ≡ γ
    e-eval a₀ (g , 3kg) i .fst x = 3kg .link a₀ x i
    e-eval a₀ (g , 3kg) i .snd .link x y = λ j → 3kg .coh₁ a₀ x y j i
    e-eval a₀ (g , 3kg) i .snd .coh₁ x y z
      = Bgpd'
          (λ _ → refl)
          (λ k j → 3kg .coh₁ a₀ x y j k)
          (λ k j → 3kg .coh₁ a₀ x z j k)
          (λ k j → 3kg .coh₁ a₀ y z j k)
          (λ _ _ → g a₀)
          (3kg .coh₁ x y z)
          i

  e-isEquiv : A → isEquiv (e {A = A})
  e-isEquiv a₀ = isoToIsEquiv (iso e (eval a₀) (e-eval a₀) λ _ → refl)

  preEquiv₂ : ∥ A ∥ → B ≃ Σ (A → B) 3-Constant
  preEquiv₂ t = e , recPropTrunc (isPropIsEquiv e) e-isEquiv t

  trunc→Gpd≃ : (∥ A ∥ → B) ≃ Σ (A → B) 3-Constant
  trunc→Gpd≃ = compEquiv (equivPi preEquiv₂) preEquiv₁

open GpdElim using (recPropTrunc→Gpd; trunc→Gpd≃) public

RecHSet : (P : A → HLevel ℓ 2) → 3-Constant P → ∥ A ∥ → HLevel ℓ 2
RecHSet P 3kP = recPropTrunc→Gpd (hLevelHLevelSuc 1) P 3kP

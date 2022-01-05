{-

This file contains:

- Eliminator for propositional truncation

-}
{-# OPTIONS --safe #-}
module Cubical.HITs.PropositionalTruncation.Properties where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

open import Cubical.Data.Sigma
open import Cubical.Data.Sum hiding (rec ; elim ; map)

open import Cubical.HITs.PropositionalTruncation.Base

private
  variable
    ℓ ℓ′ : Level
    A B C : Type ℓ
    A′ : Type ℓ′

∥∥-isPropDep : (P : A → Type ℓ) → isOfHLevelDep 1 (λ x → ∥ P x ∥)
∥∥-isPropDep P = isOfHLevel→isOfHLevelDep 1 (λ _ → squash)

rec : {P : Type ℓ} → isProp P → (A → P) → ∥ A ∥ → P
rec Pprop f ∣ x ∣ = f x
rec Pprop f (squash x y i) = Pprop (rec Pprop f x) (rec Pprop f y) i

rec2 : {P : Type ℓ} → isProp P → (A → B → P) → ∥ A ∥ → ∥ B ∥ → P
rec2 Pprop f ∣ x ∣ ∣ y ∣ = f x y
rec2 Pprop f ∣ x ∣ (squash y z i) = Pprop (rec2 Pprop f ∣ x ∣ y) (rec2 Pprop f ∣ x ∣ z) i
rec2 Pprop f (squash x y i) z = Pprop (rec2 Pprop f x z) (rec2 Pprop f y z) i

-- Old version
-- rec2 : ∀ {P : Type ℓ} → isProp P → (A → A → P) → ∥ A ∥ → ∥ A ∥ → P
-- rec2 Pprop f = rec (isProp→ Pprop) (λ a → rec Pprop (f a))

elim : {P : ∥ A ∥ → Type ℓ} → ((a : ∥ A ∥) → isProp (P a))
     → ((x : A) → P ∣ x ∣) → (a : ∥ A ∥) → P a
elim Pprop f ∣ x ∣ = f x
elim Pprop f (squash x y i) =
  isOfHLevel→isOfHLevelDep 1 Pprop
    (elim Pprop f x) (elim Pprop f y) (squash x y) i

elim2 : {P : ∥ A ∥ → ∥ B ∥ → Type ℓ}
        (Pprop : (x : ∥ A ∥) (y : ∥ B ∥) → isProp (P x y))
        (f : (a : A) (b : B) → P ∣ a ∣ ∣ b ∣)
        (x : ∥ A ∥) (y : ∥ B ∥) → P x y
elim2 Pprop f =
  elim (λ _ → isPropΠ (λ _ → Pprop _ _))
                       (λ a → elim (λ _ → Pprop _ _) (f a))

elim3 : {P : ∥ A ∥ → ∥ B ∥ → ∥ C ∥ → Type ℓ}
        (Pprop : ((x : ∥ A ∥) (y : ∥ B ∥) (z : ∥ C ∥) → isProp (P x y z)))
        (g : (a : A) (b : B) (c : C) → P (∣ a ∣) ∣ b ∣ ∣ c ∣)
        (x : ∥ A ∥) (y : ∥ B ∥) (z : ∥ C ∥) → P x y z
elim3 Pprop g = elim2 (λ _ _ → isPropΠ (λ _ → Pprop _ _ _))
                      (λ a b → elim (λ _ → Pprop _ _ _) (g a b))

isPropPropTrunc : isProp ∥ A ∥
isPropPropTrunc x y = squash x y

propTrunc≃ : A ≃ B → ∥ A ∥ ≃ ∥ B ∥
propTrunc≃ e =
  propBiimpl→Equiv
    isPropPropTrunc isPropPropTrunc
    (rec isPropPropTrunc (λ a → ∣ e .fst a ∣))
    (rec isPropPropTrunc (λ b → ∣ invEq e b ∣))

propTruncIdempotent≃ : isProp A → ∥ A ∥ ≃ A
propTruncIdempotent≃ {A = A} hA = isoToEquiv f
  where
  f : Iso ∥ A ∥ A
  Iso.fun f        = rec hA (idfun A)
  Iso.inv f x      = ∣ x ∣
  Iso.rightInv f _ = refl
  Iso.leftInv f    = elim (λ _ → isProp→isSet isPropPropTrunc _ _) (λ _ → refl)

propTruncIdempotent : isProp A → ∥ A ∥ ≡ A
propTruncIdempotent hA = ua (propTruncIdempotent≃ hA)

-- We could also define the eliminator using the recursor
elim' : {P : ∥ A ∥ → Type ℓ} → ((a : ∥ A ∥) → isProp (P a)) →
        ((x : A) → P ∣ x ∣) → (a : ∥ A ∥) → P a
elim' {P = P} Pprop f a =
  rec (Pprop a) (λ x → transp (λ i → P (squash ∣ x ∣ a i)) i0 (f x)) a

map : (A → B) → (∥ A ∥ → ∥ B ∥)
map f = rec squash (∣_∣ ∘ f)

map2 : (A → B → C) → (∥ A ∥ → ∥ B ∥ → ∥ C ∥)
map2 f = rec (isPropΠ λ _ → squash) (map ∘ f)

-- The propositional truncation can be eliminated into non-propositional
-- types as long as the function used in the eliminator is 'coherently
-- constant.' The details of this can be found in the following paper:
--
--   https://arxiv.org/pdf/1411.2682.pdf
module SetElim (Bset : isSet B) where
  Bset' : isSet' B
  Bset' = isSet→isSet' Bset

  rec→Set : (f : A → B) (kf : 2-Constant f) → ∥ A ∥ → B
  helper  : (f : A → B) (kf : 2-Constant f) → (t u : ∥ A ∥)
          → rec→Set f kf t ≡ rec→Set f kf u

  rec→Set f kf ∣ x ∣ = f x
  rec→Set f kf (squash t u i) = helper f kf t u i

  helper f kf ∣ x ∣ ∣ y ∣ = kf x y
  helper f kf (squash t u i) v
    = Bset' (helper f kf t v) (helper f kf u v) (helper f kf t u) refl i
  helper f kf t (squash u v i)
    = Bset' (helper f kf t u) (helper f kf t v) refl (helper f kf u v) i

  kcomp : (f : ∥ A ∥ → B) → 2-Constant (f ∘ ∣_∣)
  kcomp f x y = cong f (squash ∣ x ∣ ∣ y ∣)

  Fset : isSet (A → B)
  Fset = isSetΠ (const Bset)

  Kset : (f : A → B) → isSet (2-Constant f)
  Kset f = isSetΠ (λ _ → isSetΠ (λ _ → isProp→isSet (Bset _ _)))

  setRecLemma
    : (f : ∥ A ∥ → B)
    → rec→Set (f ∘ ∣_∣) (kcomp f) ≡ f
  setRecLemma f i t
    = elim {P = λ t → rec→Set (f ∘ ∣_∣) (kcomp f) t ≡ f t}
        (λ t → Bset _ _) (λ x → refl) t i

  mkKmap : (∥ A ∥ → B) → Σ (A → B) 2-Constant
  mkKmap f = f ∘ ∣_∣ , kcomp f

  fib : (g : Σ (A → B) 2-Constant) → fiber mkKmap g
  fib (g , kg) = rec→Set g kg , refl

  eqv : (g : Σ (A → B) 2-Constant) → ∀ fi → fib g ≡ fi
  eqv g (f , p) =
    Σ≡Prop (λ f → isOfHLevelΣ 2 Fset Kset _ _)
      (cong (uncurry rec→Set) (sym p) ∙ setRecLemma f)

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
  preEquiv₁ t = e , rec (isPropIsEquiv e) e-isEquiv t

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
  trunc→Set≃₂ = compEquiv (equivΠCod preEquiv₁) preEquiv₂

open SetElim public using (rec→Set; trunc→Set≃)

elim→Set
  : {P : ∥ A ∥ → Type ℓ}
  → (∀ t → isSet (P t))
  → (f : (x : A) → P ∣ x ∣)
  → (kf : ∀ x y → PathP (λ i → P (squash ∣ x ∣ ∣ y ∣ i)) (f x) (f y))
  → (t : ∥ A ∥) → P t
elim→Set {A = A} {P = P} Pset f kf t
  = rec→Set (Pset t) g gk t
  where
  g : A → P t
  g x = transp (λ i → P (squash ∣ x ∣ t i)) i0 (f x)

  gk : 2-Constant g
  gk x y i = transp (λ j → P (squash (squash ∣ x ∣ ∣ y ∣ i) t j)) i0 (kf x y i)

RecHProp : (P : A → hProp ℓ) (kP : ∀ x y → P x ≡ P y) → ∥ A ∥ → hProp ℓ
RecHProp P kP = rec→Set isSetHProp P kP

module GpdElim (Bgpd : isGroupoid B) where
  Bgpd' : isGroupoid' B
  Bgpd' = isGroupoid→isGroupoid' Bgpd

  module _ (f : A → B) (3kf : 3-Constant f) where
    open 3-Constant 3kf

    rec→Gpd : ∥ A ∥ → B
    pathHelper : (t u : ∥ A ∥) → rec→Gpd t ≡ rec→Gpd u
    triHelper₁
      : (t u v : ∥ A ∥)
      → Square (pathHelper t u) (pathHelper t v) refl (pathHelper u v)
    triHelper₂
      : (t u v : ∥ A ∥)
      → Square (pathHelper t v) (pathHelper u v) (pathHelper t u) refl

    rec→Gpd ∣ x ∣ = f x
    rec→Gpd (squash t u i) = pathHelper t u i

    pathHelper ∣ x ∣ ∣ y ∣ = link x y
    pathHelper (squash t u j) v = triHelper₂ t u v j
    pathHelper ∣ x ∣ (squash u v j) = triHelper₁ ∣ x ∣ u v j

    triHelper₁ ∣ x ∣ ∣ y ∣ ∣ z ∣ = coh₁ x y z
    triHelper₁ (squash s t i) u v
      = Bgpd'
          (triHelper₁ s u v)
          (triHelper₁ t u v)
          (triHelper₂ s t u)
          (triHelper₂ s t v)
          (λ i → refl)
          (λ i → pathHelper u v)
          i
    triHelper₁ ∣ x ∣ (squash t u i) v
      = Bgpd'
          (triHelper₁ ∣ x ∣ t v)
          (triHelper₁ ∣ x ∣ u v)
          (triHelper₁ ∣ x ∣ t u)
          (λ i → pathHelper ∣ x ∣ v)
          (λ i → refl)
          (triHelper₂ t u v)
          i
    triHelper₁ ∣ x ∣ ∣ y ∣ (squash u v i)
      = Bgpd'
          (triHelper₁ ∣ x ∣ ∣ y ∣ u)
          (triHelper₁ ∣ x ∣ ∣ y ∣ v)
          (λ i → link x y)
          (triHelper₁ ∣ x ∣ u v)
          (λ i → refl)
          (triHelper₁ ∣ y ∣ u v)
          i

    triHelper₂ ∣ x ∣ ∣ y ∣ ∣ z ∣ = coh₂ x y z
    triHelper₂ (squash s t i) u v
      = Bgpd'
          (triHelper₂ s u v)
          (triHelper₂ t u v)
          (triHelper₂ s t v)
          (λ i → pathHelper u v)
          (triHelper₂ s t u)
          (λ i → refl)
          i
    triHelper₂ ∣ x ∣ (squash t u i) v
      = Bgpd'
          (triHelper₂ ∣ x ∣ t v)
          (triHelper₂ ∣ x ∣ u v)
          (λ i → pathHelper ∣ x ∣ v)
          (triHelper₂ t u v)
          (triHelper₁ ∣ x ∣ t u)
          (λ i → refl)
          i
    triHelper₂ ∣ x ∣ ∣ y ∣ (squash u v i)
      = Bgpd'
          (triHelper₂ ∣ x ∣ ∣ y ∣ u)
          (triHelper₂ ∣ x ∣ ∣ y ∣ v)
          (triHelper₁ ∣ x ∣ u v)
          (triHelper₁ ∣ y ∣ u v)
          (λ i → link x y)
          (λ i → refl)
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
          (λ k j → f (cb k j i0) .snd .coh₁ x y z k j )
          (λ k j → f (cb k j i1) .snd .coh₁ x y z k j)
          (λ k j → f (cb i0 j k) .snd .link x y j)
          (λ k j → f (cb i1 j k) .snd .link x z j)
          (λ _ → refl)
          (λ k j → f (cb j i1 k) .snd .link y z j)
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
          (λ _ _ → g a₀)
          (3kg .coh₁ x y z)
          (λ k j → 3kg .coh₁ a₀ x y j k)
          (λ k j → 3kg .coh₁ a₀ x z j k)
          (λ _ → refl)
          (λ k j → 3kg .coh₁ a₀ y z j k)
          i

  e-isEquiv : A → isEquiv (e {A = A})
  e-isEquiv a₀ = isoToIsEquiv (iso e (eval a₀) (e-eval a₀) λ _ → refl)

  preEquiv₂ : ∥ A ∥ → B ≃ Σ (A → B) 3-Constant
  preEquiv₂ t = e , rec (isPropIsEquiv e) e-isEquiv t

  trunc→Gpd≃ : (∥ A ∥ → B) ≃ Σ (A → B) 3-Constant
  trunc→Gpd≃ = compEquiv (equivΠCod preEquiv₂) preEquiv₁

open GpdElim using (rec→Gpd; trunc→Gpd≃) public

squashᵗ
  : ∀(x y z : A)
  → Square (squash ∣ x ∣ ∣ y ∣) (squash ∣ x ∣ ∣ z ∣) refl (squash ∣ y ∣ ∣ z ∣)
squashᵗ x y z i = squash ∣ x ∣ (squash ∣ y ∣ ∣ z ∣ i)

elim→Gpd
  : (P : ∥ A ∥ → Type ℓ)
  → (∀ t → isGroupoid (P t))
  → (f : (x : A) → P ∣ x ∣)
  → (kf : ∀ x y → PathP (λ i → P (squash ∣ x ∣ ∣ y ∣ i)) (f x) (f y))
  → (3kf : ∀ x y z
         → SquareP (λ i j → P (squashᵗ x y z i j)) (kf x y) (kf x z) refl (kf y z))
  → (t : ∥ A ∥) → P t
elim→Gpd {A = A} P Pgpd f kf 3kf t = rec→Gpd (Pgpd t) g 3kg t
  where
  g : A → P t
  g x = transp (λ i → P (squash ∣ x ∣ t i)) i0 (f x)

  open 3-Constant

  3kg : 3-Constant g
  3kg .link x y i
    = transp (λ j → P (squash (squash ∣ x ∣ ∣ y ∣ i) t j)) i0 (kf x y i)
  3kg .coh₁ x y z i j
    = transp (λ k → P (squash (squashᵗ x y z i j) t k)) i0 (3kf x y z i j)

RecHSet : (P : A → TypeOfHLevel ℓ 2) → 3-Constant P → ∥ A ∥ → TypeOfHLevel ℓ 2
RecHSet P 3kP = rec→Gpd (isOfHLevelTypeOfHLevel 2) P 3kP

∥∥-IdempotentL-⊎-≃ : ∥ ∥ A ∥ ⊎ A′ ∥ ≃ ∥ A ⊎ A′ ∥
∥∥-IdempotentL-⊎-≃ = isoToEquiv ∥∥-IdempotentL-⊎-Iso
  where ∥∥-IdempotentL-⊎-Iso : Iso (∥ ∥ A ∥ ⊎ A′ ∥)  (∥ A ⊎ A′ ∥)
        Iso.fun ∥∥-IdempotentL-⊎-Iso x = rec squash lem x
          where lem : ∥ A ∥ ⊎ A′ → ∥ A ⊎ A′ ∥
                lem (inl x) = map (λ a → inl a) x
                lem (inr x) = ∣ inr x ∣
        Iso.inv ∥∥-IdempotentL-⊎-Iso x = map lem x
          where lem : A ⊎ A′ → ∥ A ∥ ⊎ A′
                lem (inl x) = inl ∣ x ∣
                lem (inr x) = inr x
        Iso.rightInv ∥∥-IdempotentL-⊎-Iso x = squash (Iso.fun ∥∥-IdempotentL-⊎-Iso (Iso.inv ∥∥-IdempotentL-⊎-Iso x)) x
        Iso.leftInv ∥∥-IdempotentL-⊎-Iso x  = squash (Iso.inv ∥∥-IdempotentL-⊎-Iso (Iso.fun ∥∥-IdempotentL-⊎-Iso x)) x

∥∥-IdempotentL-⊎ : ∥ ∥ A ∥ ⊎ A′ ∥ ≡ ∥ A ⊎ A′ ∥
∥∥-IdempotentL-⊎ = ua ∥∥-IdempotentL-⊎-≃

∥∥-IdempotentR-⊎-≃ : ∥ A ⊎ ∥ A′ ∥ ∥ ≃ ∥ A ⊎ A′ ∥
∥∥-IdempotentR-⊎-≃ = isoToEquiv ∥∥-IdempotentR-⊎-Iso
  where ∥∥-IdempotentR-⊎-Iso : Iso (∥ A ⊎ ∥ A′ ∥ ∥) (∥ A ⊎ A′ ∥)
        Iso.fun ∥∥-IdempotentR-⊎-Iso x = rec squash lem x
          where lem : A ⊎ ∥ A′ ∥ → ∥ A ⊎ A′ ∥
                lem (inl x) = ∣ inl x ∣
                lem (inr x) = map (λ a → inr a) x
        Iso.inv ∥∥-IdempotentR-⊎-Iso x = map lem x
          where lem : A ⊎ A′ → A ⊎ ∥ A′ ∥
                lem (inl x) = inl x
                lem (inr x) = inr ∣ x ∣
        Iso.rightInv ∥∥-IdempotentR-⊎-Iso x = squash (Iso.fun ∥∥-IdempotentR-⊎-Iso (Iso.inv ∥∥-IdempotentR-⊎-Iso x)) x
        Iso.leftInv ∥∥-IdempotentR-⊎-Iso x  = squash (Iso.inv ∥∥-IdempotentR-⊎-Iso (Iso.fun ∥∥-IdempotentR-⊎-Iso x)) x

∥∥-IdempotentR-⊎ : ∥ A ⊎ ∥ A′ ∥ ∥ ≡ ∥ A ⊎ A′ ∥
∥∥-IdempotentR-⊎ = ua ∥∥-IdempotentR-⊎-≃

∥∥-Idempotent-⊎ : {A : Type ℓ} {A′ : Type ℓ′} → ∥ ∥ A ∥ ⊎ ∥ A′ ∥ ∥ ≡ ∥ A ⊎ A′ ∥
∥∥-Idempotent-⊎ {A = A} {A′} = ∥ ∥ A ∥ ⊎ ∥ A′ ∥ ∥ ≡⟨ ∥∥-IdempotentR-⊎ ⟩
                               ∥ ∥ A ∥ ⊎ A′ ∥     ≡⟨ ∥∥-IdempotentL-⊎ ⟩
                               ∥ A ⊎ A′ ∥         ∎

∥∥-IdempotentL-×-≃ : ∥ ∥ A ∥ × A′ ∥ ≃ ∥ A × A′ ∥
∥∥-IdempotentL-×-≃ = isoToEquiv ∥∥-IdempotentL-×-Iso
  where ∥∥-IdempotentL-×-Iso : Iso (∥ ∥ A ∥ × A′ ∥) (∥ A × A′ ∥)
        Iso.fun ∥∥-IdempotentL-×-Iso x = rec squash lem x
          where lem : ∥ A ∥ × A′ → ∥ A × A′ ∥
                lem (a , a′) = map2 (λ a a′ → a , a′) a ∣ a′ ∣
        Iso.inv ∥∥-IdempotentL-×-Iso x = map lem x
          where lem : A × A′ → ∥ A ∥ × A′
                lem (a , a′) = ∣ a ∣ , a′
        Iso.rightInv ∥∥-IdempotentL-×-Iso x = squash (Iso.fun ∥∥-IdempotentL-×-Iso (Iso.inv ∥∥-IdempotentL-×-Iso x)) x
        Iso.leftInv ∥∥-IdempotentL-×-Iso x  = squash (Iso.inv ∥∥-IdempotentL-×-Iso (Iso.fun ∥∥-IdempotentL-×-Iso x)) x

∥∥-IdempotentL-× : ∥ ∥ A ∥ × A′ ∥ ≡ ∥ A × A′ ∥
∥∥-IdempotentL-× = ua ∥∥-IdempotentL-×-≃

∥∥-IdempotentR-×-≃ : ∥ A × ∥ A′ ∥ ∥ ≃ ∥ A × A′ ∥
∥∥-IdempotentR-×-≃ = isoToEquiv ∥∥-IdempotentR-×-Iso
  where ∥∥-IdempotentR-×-Iso : Iso (∥ A × ∥ A′ ∥ ∥) (∥ A × A′ ∥)
        Iso.fun ∥∥-IdempotentR-×-Iso x = rec squash lem x
          where lem : A × ∥ A′ ∥ → ∥ A × A′ ∥
                lem (a , a′) = map2 (λ a a′ → a , a′) ∣ a ∣ a′
        Iso.inv ∥∥-IdempotentR-×-Iso x = map lem x
          where lem : A × A′ → A × ∥ A′ ∥
                lem (a , a′) = a , ∣ a′ ∣
        Iso.rightInv ∥∥-IdempotentR-×-Iso x = squash (Iso.fun ∥∥-IdempotentR-×-Iso (Iso.inv ∥∥-IdempotentR-×-Iso x)) x
        Iso.leftInv ∥∥-IdempotentR-×-Iso x  = squash (Iso.inv ∥∥-IdempotentR-×-Iso (Iso.fun ∥∥-IdempotentR-×-Iso x)) x

∥∥-IdempotentR-× : ∥ A × ∥ A′ ∥ ∥ ≡ ∥ A × A′ ∥
∥∥-IdempotentR-× = ua ∥∥-IdempotentR-×-≃

∥∥-Idempotent-× : {A : Type ℓ} {A′ : Type ℓ′} → ∥ ∥ A ∥ × ∥ A′ ∥ ∥ ≡ ∥ A × A′ ∥
∥∥-Idempotent-× {A = A} {A′} = ∥ ∥ A ∥ × ∥ A′ ∥ ∥ ≡⟨ ∥∥-IdempotentR-× ⟩
                               ∥ ∥ A ∥ × A′ ∥     ≡⟨ ∥∥-IdempotentL-× ⟩
                               ∥ A × A′ ∥         ∎

∥∥-Idempotent-×-≃ : {A : Type ℓ} {A′ : Type ℓ′} → ∥ ∥ A ∥ × ∥ A′ ∥ ∥ ≃ ∥ A × A′ ∥
∥∥-Idempotent-×-≃ {A = A} {A′} = compEquiv ∥∥-IdempotentR-×-≃ ∥∥-IdempotentL-×-≃

∥∥-×-≃ : {A : Type ℓ} {A′ : Type ℓ′} → ∥ A ∥ × ∥ A′ ∥ ≃ ∥ A × A′ ∥
∥∥-×-≃ {A = A} {A′} = compEquiv (invEquiv (propTruncIdempotent≃ (isProp× isPropPropTrunc isPropPropTrunc))) ∥∥-Idempotent-×-≃

∥∥-× : {A : Type ℓ} {A′ : Type ℓ′} → ∥ A ∥ × ∥ A′ ∥ ≡ ∥ A × A′ ∥
∥∥-× = ua ∥∥-×-≃

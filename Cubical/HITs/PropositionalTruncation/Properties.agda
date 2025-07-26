{-

This file contains:

- Eliminator for propositional truncation

-}
{-# OPTIONS --safe #-}
module Cubical.HITs.PropositionalTruncation.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

open import Cubical.Data.Sigma
open import Cubical.Data.Sum hiding (rec ; elim ; map)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.FinData using (Fin ; zero ; suc)

open import Cubical.HITs.PropositionalTruncation.Base

private
  variable
    ℓ ℓ' : Level
    A B C D : Type ℓ
    A′ : Type ℓ'

∥∥-isPropDep : (P : A → Type ℓ) → isOfHLevelDep 1 (λ x → ∥ P x ∥₁)
∥∥-isPropDep P = isOfHLevel→isOfHLevelDep 1 (λ _ → squash₁)

rec : {P : Type ℓ} → isProp P → (A → P) → ∥ A ∥₁ → P
rec Pprop f ∣ x ∣₁ = f x
rec Pprop f (squash₁ x y i) = Pprop (rec Pprop f x) (rec Pprop f y) i

rec2 : {P : Type ℓ} → isProp P → (A → B → P) → ∥ A ∥₁ → ∥ B ∥₁ → P
rec2 Pprop f ∣ x ∣₁ ∣ y ∣₁ = f x y
rec2 Pprop f ∣ x ∣₁ (squash₁ y z i) = Pprop (rec2 Pprop f ∣ x ∣₁ y) (rec2 Pprop f ∣ x ∣₁ z) i
rec2 Pprop f (squash₁ x y i) z = Pprop (rec2 Pprop f x z) (rec2 Pprop f y z) i

rec3 : {P : Type ℓ} → isProp P → (A → B → C → P) → ∥ A ∥₁ → ∥ B ∥₁ → ∥ C ∥₁ → P
rec3 Pprop f ∣ x ∣₁ ∣ y ∣₁ ∣ z ∣₁ = f x y z
rec3 Pprop f ∣ x ∣₁ ∣ y ∣₁ (squash₁ z w i) = Pprop (rec3 Pprop f ∣ x ∣₁ ∣ y ∣₁ z) (rec3 Pprop f ∣ x ∣₁ ∣ y ∣₁ w) i
rec3 Pprop f ∣ x ∣₁ (squash₁ y z i) w = Pprop (rec3 Pprop f ∣ x ∣₁ y w) (rec3 Pprop f ∣ x ∣₁ z w) i
rec3 Pprop f (squash₁ x y i) z w = Pprop (rec3 Pprop f x z w) (rec3 Pprop f y z w) i

∃-rec : {B : A → Type ℓ'} {P : Type ℓ} → isProp P → (∀ x → B x → P) → ∃[ x ∈ A ] B x → P
∃-rec Pprop f = rec Pprop (uncurry f)

-- Old version
-- rec2 : ∀ {P : Type ℓ} → isProp P → (A → A → P) → ∥ A ∥ → ∥ A ∥ → P
-- rec2 Pprop f = rec (isProp→ Pprop) (λ a → rec Pprop (f a))

-- n-ary recursor, stated using a dependent FinVec
recFin : {m : ℕ} {P : Fin m → Type ℓ}
         {B : Type ℓ'} (isPropB : isProp B)
       → ((∀ i → P i) → B)
      ---------------------
       → ((∀ i → ∥ P i ∥₁) → B)
recFin {m = zero} _ untruncHyp _ = untruncHyp (λ ())
recFin {m = suc m} {P = P} {B = B} isPropB untruncHyp truncFam =
  curriedishTrunc (truncFam zero) (truncFam ∘ suc)
  where
  curriedish : P zero → (∀ i → ∥ P (suc i) ∥₁) → B
  curriedish p₀ = recFin isPropB
                         (λ famSuc → untruncHyp (λ { zero → p₀ ; (suc i) → famSuc i }))

  curriedishTrunc : ∥ P zero ∥₁ → (∀ i → ∥ P (suc i) ∥₁) → B
  curriedishTrunc = rec (isProp→ isPropB) curriedish

recFin2 : {m1 m2 : ℕ} {P : Fin m1 → Fin m2 → Type ℓ}
          {B : Type ℓ'} (isPropB : isProp B)
        → ((∀ i j → P i j) → B)
       --------------------------
        → (∀ i j → ∥ P i j ∥₁)
        → B
recFin2 {m1 = zero} _ untruncHyp _ = untruncHyp λ ()
recFin2 {m1 = suc m1} {P = P} {B = B} isPropB untruncHyp truncFam =
  curriedishTrunc (truncFam zero) (truncFam ∘ suc)
  where
  curriedish : (∀ j → P zero j) → (∀ i j → ∥ P (suc i) j ∥₁) → B
  curriedish p₀ truncFamSuc = recFin2 isPropB
                             (λ famSuc → untruncHyp λ { zero → p₀ ; (suc i) → famSuc i })
                               truncFamSuc

  curriedishTrunc : (∀ j → ∥ P zero j ∥₁) → (∀ i j → ∥ P (suc i) j ∥₁) → B
  curriedishTrunc = recFin (isProp→ isPropB) curriedish


elim : {P : ∥ A ∥₁ → Type ℓ} → ((a : ∥ A ∥₁) → isProp (P a))
     → ((x : A) → P ∣ x ∣₁) → (a : ∥ A ∥₁) → P a
elim Pprop f ∣ x ∣₁ = f x
elim Pprop f (squash₁ x y i) =
  isOfHLevel→isOfHLevelDep 1 Pprop
    (elim Pprop f x) (elim Pprop f y) (squash₁ x y) i

elim2 : {P : ∥ A ∥₁ → ∥ B ∥₁ → Type ℓ}
        (Pprop : (x : ∥ A ∥₁) (y : ∥ B ∥₁) → isProp (P x y))
        (f : (a : A) (b : B) → P ∣ a ∣₁ ∣ b ∣₁)
        (x : ∥ A ∥₁) (y : ∥ B ∥₁) → P x y
elim2 Pprop f =
  elim (λ _ → isPropΠ (λ _ → Pprop _ _))
                       (λ a → elim (λ _ → Pprop _ _) (f a))

elim3 : {P : ∥ A ∥₁ → ∥ B ∥₁ → ∥ C ∥₁ → Type ℓ}
        (Pprop : ((x : ∥ A ∥₁) (y : ∥ B ∥₁) (z : ∥ C ∥₁) → isProp (P x y z)))
        (g : (a : A) (b : B) (c : C) → P (∣ a ∣₁) ∣ b ∣₁ ∣ c ∣₁)
        (x : ∥ A ∥₁) (y : ∥ B ∥₁) (z : ∥ C ∥₁) → P x y z
elim3 Pprop g = elim2 (λ _ _ → isPropΠ (λ _ → Pprop _ _ _))
                      (λ a b → elim (λ _ → Pprop _ _ _) (g a b))

-- n-ary eliminator, stated using a dependent FinVec
elimFin : {m : ℕ} {P : Fin m → Type ℓ}
          {B : (∀ i → ∥ P i ∥₁) → Type ℓ'}
          (isPropB : ∀ x → isProp (B x))
        → ((x : ∀ i → P i) → B (λ i → ∣ x i ∣₁))
       ----------------------------------------
        → ((x : ∀ i → ∥ P i ∥₁) → B x)
elimFin {m = zero} {B = B} _ untruncHyp _ = subst B (funExt (λ ())) (untruncHyp (λ ()))
elimFin {m = suc m} {P = P} {B = B} isPropB untruncHyp x =
  subst B (funExt (λ { zero → refl ; (suc i) → refl}))
          (curriedishTrunc (x zero) (x ∘ suc))
  where
  curriedish : (x₀ : P zero) (xₛ : ∀ i → ∥ P (suc i) ∥₁)
             → B (λ { zero → ∣ x₀ ∣₁ ; (suc i) → xₛ i})
  curriedish x₀ xₛ = subst B (funExt (λ { zero → refl ; (suc i) → refl}))
     (elimFin (λ xₛ → isPropB (λ { zero → ∣ x₀ ∣₁ ; (suc i) → xₛ i}))
              (λ y → subst B (funExt (λ { zero → refl ; (suc i) → refl}))
                             (untruncHyp (λ { zero → x₀ ; (suc i) → y i }))) xₛ)

  curriedishTrunc : (x₀ : ∥ P zero ∥₁) (xₛ : ∀ i → ∥ P (suc i) ∥₁)
                  → B (λ { zero → x₀ ; (suc i) → xₛ i})
  curriedishTrunc = elim (λ _ → isPropΠ λ _ → isPropB _)
                    λ x₀ xₛ → subst B (funExt (λ { zero → refl ; (suc i) → refl}))
                                      (curriedish x₀ xₛ)

∃-elim : {B : A → Type ℓ'} {P : ∃[ x ∈ A ] B x → Type ℓ} (Pprop : ∀ s → isProp (P s))
       → (∀ x y → P ∣ x , y ∣₁) → ∀ s → P s
∃-elim Pprop f = elim Pprop (uncurry f)

isPropPropTrunc : isProp ∥ A ∥₁
isPropPropTrunc x y = squash₁ x y

propTrunc≃ : A ≃ B → ∥ A ∥₁ ≃ ∥ B ∥₁
propTrunc≃ e =
  propBiimpl→Equiv
    isPropPropTrunc isPropPropTrunc
    (rec isPropPropTrunc (λ a → ∣ e .fst a ∣₁))
    (rec isPropPropTrunc (λ b → ∣ invEq e b ∣₁))

propTruncIdempotent≃ : isProp A → ∥ A ∥₁ ≃ A
propTruncIdempotent≃ {A = A} hA = isoToEquiv f
  where
  f : Iso ∥ A ∥₁ A
  Iso.fun f        = rec hA (idfun A)
  Iso.inv f x      = ∣ x ∣₁
  Iso.rightInv f _ = refl
  Iso.leftInv f    = elim (λ _ → isProp→isSet isPropPropTrunc _ _) (λ _ → refl)

propTruncIdempotent : isProp A → ∥ A ∥₁ ≡ A
propTruncIdempotent hA = ua (propTruncIdempotent≃ hA)

-- We could also define the eliminator using the recursor
elim' : {P : ∥ A ∥₁ → Type ℓ} → ((a : ∥ A ∥₁) → isProp (P a)) →
        ((x : A) → P ∣ x ∣₁) → (a : ∥ A ∥₁) → P a
elim' {P = P} Pprop f a =
  rec (Pprop a) (λ x → transp (λ i → P (squash₁ ∣ x ∣₁ a i)) i0 (f x)) a

map : (A → B) → (∥ A ∥₁ → ∥ B ∥₁)
map f = rec squash₁ (∣_∣₁ ∘ f)

map2 : (A → B → C) → (∥ A ∥₁ → ∥ B ∥₁ → ∥ C ∥₁)
map2 f = rec (isPropΠ λ _ → squash₁) (map ∘ f)

map3 : (A → B → C → D) → (∥ A ∥₁ → ∥ B ∥₁ → ∥ C ∥₁ → ∥ D ∥₁)
map3 f = rec (isPropΠ2 λ _ _ → squash₁) (map2 ∘ f)

-- The propositional truncation can be eliminated into non-propositional
-- types as long as the function used in the eliminator is 'coherently
-- constant.' The details of this can be found in the following paper:
--
--   https://arxiv.org/pdf/1411.2682.pdf
module SetElim (Bset : isSet B) where
  Bset' : isSet' B
  Bset' = isSet→isSet' Bset

  rec→Set : (f : A → B) (kf : 2-Constant f) → ∥ A ∥₁ → B
  helper  : (f : A → B) (kf : 2-Constant f) → (t u : ∥ A ∥₁)
          → rec→Set f kf t ≡ rec→Set f kf u

  rec→Set f kf ∣ x ∣₁ = f x
  rec→Set f kf (squash₁ t u i) = helper f kf t u i

  helper f kf ∣ x ∣₁ ∣ y ∣₁ = kf x y
  helper f kf (squash₁ t u i) v
    = Bset' (helper f kf t v) (helper f kf u v) (helper f kf t u) refl i
  helper f kf t (squash₁ u v i)
    = Bset' (helper f kf t u) (helper f kf t v) refl (helper f kf u v) i

  kcomp : (f : ∥ A ∥₁ → B) → 2-Constant (f ∘ ∣_∣₁)
  kcomp f x y = cong f (squash₁ ∣ x ∣₁ ∣ y ∣₁)

  Fset : isSet (A → B)
  Fset = isSetΠ (const Bset)

  Kset : (f : A → B) → isSet (2-Constant f)
  Kset f = isSetΠ (λ _ → isSetΠ (λ _ → isProp→isSet (Bset _ _)))

  setRecLemma
    : (f : ∥ A ∥₁ → B)
    → rec→Set (f ∘ ∣_∣₁) (kcomp f) ≡ f
  setRecLemma f i t
    = elim {P = λ t → rec→Set (f ∘ ∣_∣₁) (kcomp f) t ≡ f t}
        (λ t → Bset _ _) (λ x → refl) t i

  mkKmap : (∥ A ∥₁ → B) → Σ (A → B) 2-Constant
  mkKmap f = f ∘ ∣_∣₁ , kcomp f

  fib : (g : Σ (A → B) 2-Constant) → fiber mkKmap g
  fib (g , kg) = rec→Set g kg , refl

  eqv : (g : Σ (A → B) 2-Constant) → ∀ fi → fib g ≡ fi
  eqv g (f , p) =
    Σ≡Prop (λ f → isOfHLevelΣ 2 Fset Kset _ _)
      (cong (uncurry rec→Set) (sym p) ∙ setRecLemma f)

  trunc→Set≃ : (∥ A ∥₁ → B) ≃ (Σ (A → B) 2-Constant)
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

  preEquiv₁ : ∥ A ∥₁ → B ≃ Σ (A → B) 2-Constant
  preEquiv₁ t = e , rec (isPropIsEquiv e) e-isEquiv t

  preEquiv₂ : (∥ A ∥₁ → Σ (A → B) 2-Constant) ≃ Σ (A → B) 2-Constant
  preEquiv₂ = isoToEquiv (iso to const (λ _ → refl) retr)
    where
    to : (∥ A ∥₁ → Σ (A → B) 2-Constant) → Σ (A → B) 2-Constant
    to f .fst x = f ∣ x ∣₁ .fst x
    to f .snd x y i = f (squash₁ ∣ x ∣₁ ∣ y ∣₁ i) .snd x y i

    retr : retract to const
    retr f i t .fst x = f (squash₁ ∣ x ∣₁ t i) .fst x
    retr f i t .snd x y
      = Bset'
          (λ j → f (squash₁ ∣ x ∣₁ ∣ y ∣₁ j) .snd x y j)
          (f t .snd x y)
          (λ j → f (squash₁ ∣ x ∣₁ t j) .fst x)
          (λ j → f (squash₁ ∣ y ∣₁ t j) .fst y)
          i

  trunc→Set≃₂ : (∥ A ∥₁ → B) ≃ Σ (A → B) 2-Constant
  trunc→Set≃₂ = compEquiv (equivΠCod preEquiv₁) preEquiv₂

open SetElim public using (rec→Set; trunc→Set≃)

elim→Set : ∀ {ℓ'} {A : Type ℓ'} {P : ∥ A ∥₁ → Type ℓ}
  → (∀ t → isSet (P t))
  → (f : (x : A) → P ∣ x ∣₁)
  → (kf : ∀ x y → PathP (λ i → P (squash₁ ∣ x ∣₁ ∣ y ∣₁ i)) (f x) (f y))
  → (t : ∥ A ∥₁) → P t
elim→Set {A = A} {P = P} Pset f kf t = main t .fst .fst
  where
  main : (t : ∥ A ∥₁)
    → isContr (Σ[ x ∈ P t ]
                ((a : A) → PathP (λ i → P (squash₁ t ∣ a ∣₁ i)) x (f a)))
  main = elim (λ _ → isPropIsContr)
    λ a →
       (((f a) , kf a)
      , λ {(x , p) → Σ≡Prop (λ _ → isPropΠ
           λ _ → isOfHLevelPathP' 1 (Pset _) _ _)
             (sym (transport (λ j → PathP (λ i → P (sq a j i)) x (f a)) (p a)))
             })
    where
    sq : (a : A) → squash₁ ∣ a ∣₁ ∣ a ∣₁ ≡ refl
    sq a = isProp→isSet squash₁ _ _ _ _

elim2→Set :
    {P : ∥ A ∥₁ → ∥ B ∥₁ → Type ℓ}
  → (∀ t u → isSet (P t u))
  → (f : (x : A) (y : B) → P ∣ x ∣₁ ∣ y ∣₁)
  → (kf₁ : ∀ x y v → PathP (λ i → P (squash₁ ∣ x ∣₁ ∣ y ∣₁ i) ∣ v ∣₁) (f x v) (f y v))
  → (kf₂ : ∀ x v w → PathP (λ i → P ∣ x ∣₁ (squash₁ ∣ v ∣₁ ∣ w ∣₁ i)) (f x v) (f x w))
  → (sf : ∀ x y v w → SquareP (λ i j → P (squash₁ ∣ x ∣₁ ∣ y ∣₁ i) (squash₁ ∣ v ∣₁ ∣ w ∣₁ j))
                              (kf₂ x v w) (kf₂ y v w) (kf₁ x y v) (kf₁ x y w))
  → (t : ∥ A ∥₁) → (u : ∥ B ∥₁) → P t u
elim2→Set {A = A} {B = B} {P = P} Pset f kf₁ kf₂ sf =
  elim→Set (λ _ → isSetΠ (λ _ → Pset _ _)) mapHelper squareHelper
  where
  mapHelper : (x : A) (u : ∥ B ∥₁) → P ∣ x ∣₁ u
  mapHelper x = elim→Set (λ _ → Pset _ _) (f x) (kf₂ x)

  squareHelper : (x y : A)
               → PathP (λ i → (u : ∥ B ∥₁) → P (squash₁ ∣ x ∣₁ ∣ y ∣₁ i) u) (mapHelper x) (mapHelper y)
  squareHelper x y i = elim→Set (λ _ → Pset _ _) (λ v → kf₁ x y v i) λ v w → sf x y v w i

RecHProp : (P : A → hProp ℓ) (kP : ∀ x y → P x ≡ P y) → ∥ A ∥₁ → hProp ℓ
RecHProp P kP = rec→Set isSetHProp P kP

squash₁ᵗ
  : ∀(x y z : A)
  → Square (squash₁ ∣ x ∣₁ ∣ y ∣₁) (squash₁ ∣ x ∣₁ ∣ z ∣₁) refl (squash₁ ∣ y ∣₁ ∣ z ∣₁)
squash₁ᵗ x y z i = squash₁ ∣ x ∣₁ (squash₁ ∣ y ∣₁ ∣ z ∣₁ i)

module _ (B : ∥ A ∥₁ → Type ℓ)
  (B-gpd : (a : _) → isGroupoid (B a))
  (f : (a : A) → B ∣ a ∣₁)
  (f-coh : (x y : A) → PathP (λ i → B (squash₁ ∣ x ∣₁ ∣ y ∣₁ i)) (f x) (f y))
  (f-coh-coh : (x y z : A) → SquareP
      (λ i j → B (squash₁ ∣ x ∣₁ (squash₁ ∣ y ∣₁ ∣ z ∣₁ i) j))
      (f-coh x y) (f-coh x z) refl (f-coh y z))
  where
  elim→Gpd : (t : ∥ A ∥₁) → B t
  private
    pathHelper : (t u : ∥ A ∥₁) → PathP (λ i → B (squash₁ t u i)) (elim→Gpd t) (elim→Gpd u)
    triHelper₁
      : (t u v : ∥ A ∥₁)
      → SquareP (λ i j → B (squash₁ t (squash₁ u v i) j))
                (pathHelper t u) (pathHelper t v)
                refl (pathHelper u v)
    triHelper₂
      : (t u v : ∥ A ∥₁)
      → SquareP (λ i j → B (squash₁ (squash₁ t u i) v j))
                (pathHelper t v) (pathHelper u v)
                (pathHelper t u) refl
    triHelper₂Cube : (x y z : ∥ A ∥₁)
      → Cube (λ j k → squash₁ x z (k ∧ j))
              (λ j k → squash₁ y z j)
              (λ i k → squash₁ x y i)
              (λ i k → squash₁ x z (i ∨ k))
              (λ i j → squash₁ x (squash₁ y z j) i)
              (λ i j → squash₁ (squash₁ x y i) z j)

    elim→Gpd ∣ x ∣₁ = f x
    elim→Gpd (squash₁ t u i) = pathHelper t u i
    triHelper₂Cube x y z =
      isProp→PathP (λ _ → isOfHLevelPathP 1 (isOfHLevelPath 1 squash₁ _ _) _ _) _ _

    pathHelper ∣ x ∣₁ ∣ y ∣₁ = f-coh x y
    pathHelper (squash₁ t u j) v = triHelper₂ t u v j
    pathHelper ∣ x ∣₁ (squash₁ u v j) = triHelper₁ ∣ x ∣₁ u v j

    triHelper₁ ∣ x ∣₁ ∣ y ∣₁ ∣ z ∣₁ = f-coh-coh x y z
    triHelper₁ (squash₁ s t i) u v
      = isGroupoid→CubeP (λ i i₁ j → B (squash₁ (squash₁ s t i) (squash₁ u v i₁) j))
                          (triHelper₁ s u v) (triHelper₁ t u v)
                          (triHelper₂ s t u)
                          (triHelper₂ s t v)
                          (λ i j → pathHelper s t i)
                          (λ i j → pathHelper u v j)
                          (B-gpd v) i

    triHelper₁ ∣ x ∣₁ (squash₁ t u i) v
      = isGroupoid→CubeP (λ i i₁ j → B (squash₁ ∣ x ∣₁ (squash₁ (squash₁ t u i) v i₁) j))
                          (triHelper₁ ∣ x ∣₁ t v) (triHelper₁ ∣ x ∣₁ u v)
                          (triHelper₁ ∣ x ∣₁ t u)
                          (λ i j → pathHelper ∣ x ∣₁ v j)
                          refl (triHelper₂ t u v)
                          (B-gpd v) i
    triHelper₁ ∣ x ∣₁ ∣ y ∣₁ (squash₁ u v i)
      = isGroupoid→CubeP (λ i i₁ j → B (squash₁ ∣ x ∣₁ (squash₁ ∣ y ∣₁ (squash₁ u v i) i₁) j))
                          (triHelper₁ ∣ x ∣₁ ∣ y ∣₁ u) (triHelper₁ ∣ x ∣₁ ∣ y ∣₁ v)
                          (λ i j → f-coh x y j) (triHelper₁ ∣ x ∣₁ u v)
                          refl (triHelper₁ ∣ y ∣₁ u v)
                          (B-gpd v) i
    triHelper₂ ∣ x ∣₁ ∣ y ∣₁ ∣ z ∣₁ i j =
      comp (λ k → B (triHelper₂Cube ∣ x ∣₁ ∣ y ∣₁ ∣ z ∣₁ i j k))
           (λ k → λ {(i = i0) → f-coh x z (k ∧ j)
                    ; (i = i1) → f-coh y z j
                    ; (j = i0) → f-coh x y i
                    ; (j = i1) → f-coh x z (i ∨ k)})
           (f-coh-coh x y z j i)
    triHelper₂ (squash₁ s t i) u v
      = isGroupoid→CubeP (λ i i₁ j → B (squash₁ (squash₁ (squash₁ s t i) u i₁) v j))
                          (triHelper₂ s u v) (triHelper₂ t u v)
                          (triHelper₂ s t v) (λ i j → pathHelper u v j)
                          (triHelper₂ s t u) refl
                          (B-gpd v) i
    triHelper₂ ∣ x ∣₁ (squash₁ t u i) v
      = isGroupoid→CubeP (λ i i₁ j → B (squash₁ (squash₁ ∣ x ∣₁ (squash₁ t u i) i₁) v j))
                          (triHelper₂ ∣ x ∣₁ t v) (triHelper₂ ∣ x ∣₁ u v)
                          (λ i j → pathHelper ∣ x ∣₁ v j) (triHelper₂ t u v)
                          (triHelper₁ ∣ x ∣₁ t u) refl
                          (B-gpd v) i
    triHelper₂ ∣ x ∣₁ ∣ y ∣₁ (squash₁ u v i)
      = isGroupoid→CubeP (λ i i₁ j → B (squash₁ (squash₁ ∣ x ∣₁ ∣ y ∣₁ i₁) (squash₁ u v i) j))
                          (triHelper₂ ∣ x ∣₁ ∣ y ∣₁ u) (triHelper₂ ∣ x ∣₁ ∣ y ∣₁ v)
                          (triHelper₁ ∣ x ∣₁ u v) (triHelper₁ ∣ y ∣₁ u v)
                          refl (λ i j → pathHelper u v i)
                          (B-gpd v) i


module GpdElim (Bgpd : isGroupoid B) where
  Bgpd' : isGroupoid' B
  Bgpd' = isGroupoid→isGroupoid' Bgpd

  module _ (f : A → B) (3kf : 3-Constant f) where
    open 3-Constant 3kf

    rec→Gpd : ∥ A ∥₁ → B
    rec→Gpd = elim→Gpd (λ _ → B) (λ _ → Bgpd) f link coh₁

  preEquiv₁ : (∥ A ∥₁ → Σ (A → B) 3-Constant) ≃ Σ (A → B) 3-Constant
  preEquiv₁ = isoToEquiv (iso fn const (λ _ → refl) retr)
    where
    open 3-Constant

    fn : (∥ A ∥₁ → Σ (A → B) 3-Constant) → Σ (A → B) 3-Constant
    fn f .fst x = f ∣ x ∣₁ .fst x
    fn f .snd .link x y i = f (squash₁ ∣ x ∣₁ ∣ y ∣₁ i) .snd .link x y i
    fn f .snd .coh₁ x y z i j
      = f (squash₁ ∣ x ∣₁ (squash₁ ∣ y ∣₁ ∣ z ∣₁ i) j) .snd .coh₁ x y z i j

    retr : retract fn const
    retr f i t .fst x = f (squash₁ ∣ x ∣₁ t i) .fst x
    retr f i t .snd .link x y j
      = f (squash₁ (squash₁ ∣ x ∣₁ ∣ y ∣₁ j) t i) .snd .link x y j
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
      cb : I → I → I → ∥ _ ∥₁
      cb i j k = squash₁ (squash₁ ∣ x ∣₁ (squash₁ ∣ y ∣₁ ∣ z ∣₁ i) j) t k

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

  preEquiv₂ : ∥ A ∥₁ → B ≃ Σ (A → B) 3-Constant
  preEquiv₂ t = e , rec (isPropIsEquiv e) e-isEquiv t

  trunc→Gpd≃ : (∥ A ∥₁ → B) ≃ Σ (A → B) 3-Constant
  trunc→Gpd≃ = compEquiv (equivΠCod preEquiv₂) preEquiv₁

open GpdElim using (rec→Gpd; trunc→Gpd≃) public

RecHSet : (P : A → TypeOfHLevel ℓ 2) → 3-Constant P → ∥ A ∥₁ → TypeOfHLevel ℓ 2
RecHSet P 3kP = rec→Gpd (isOfHLevelTypeOfHLevel 2) P 3kP

∥∥-IdempotentL-⊎-≃ : ∥ ∥ A ∥₁ ⊎ A′ ∥₁ ≃ ∥ A ⊎ A′ ∥₁
∥∥-IdempotentL-⊎-≃ = isoToEquiv ∥∥-IdempotentL-⊎-Iso
  where ∥∥-IdempotentL-⊎-Iso : Iso (∥ ∥ A ∥₁ ⊎ A′ ∥₁)  (∥ A ⊎ A′ ∥₁)
        Iso.fun ∥∥-IdempotentL-⊎-Iso x = rec squash₁ lem x
          where lem : ∥ A ∥₁ ⊎ A′ → ∥ A ⊎ A′ ∥₁
                lem (inl x) = map (λ a → inl a) x
                lem (inr x) = ∣ inr x ∣₁
        Iso.inv ∥∥-IdempotentL-⊎-Iso x = map lem x
          where lem : A ⊎ A′ → ∥ A ∥₁ ⊎ A′
                lem (inl x) = inl ∣ x ∣₁
                lem (inr x) = inr x
        Iso.rightInv ∥∥-IdempotentL-⊎-Iso x = squash₁ (Iso.fun ∥∥-IdempotentL-⊎-Iso (Iso.inv ∥∥-IdempotentL-⊎-Iso x)) x
        Iso.leftInv ∥∥-IdempotentL-⊎-Iso x  = squash₁ (Iso.inv ∥∥-IdempotentL-⊎-Iso (Iso.fun ∥∥-IdempotentL-⊎-Iso x)) x

∥∥-IdempotentL-⊎ : ∥ ∥ A ∥₁ ⊎ A′ ∥₁ ≡ ∥ A ⊎ A′ ∥₁
∥∥-IdempotentL-⊎ = ua ∥∥-IdempotentL-⊎-≃

∥∥-IdempotentR-⊎-≃ : ∥ A ⊎ ∥ A′ ∥₁ ∥₁ ≃ ∥ A ⊎ A′ ∥₁
∥∥-IdempotentR-⊎-≃ = isoToEquiv ∥∥-IdempotentR-⊎-Iso
  where ∥∥-IdempotentR-⊎-Iso : Iso (∥ A ⊎ ∥ A′ ∥₁ ∥₁) (∥ A ⊎ A′ ∥₁)
        Iso.fun ∥∥-IdempotentR-⊎-Iso x = rec squash₁ lem x
          where lem : A ⊎ ∥ A′ ∥₁ → ∥ A ⊎ A′ ∥₁
                lem (inl x) = ∣ inl x ∣₁
                lem (inr x) = map (λ a → inr a) x
        Iso.inv ∥∥-IdempotentR-⊎-Iso x = map lem x
          where lem : A ⊎ A′ → A ⊎ ∥ A′ ∥₁
                lem (inl x) = inl x
                lem (inr x) = inr ∣ x ∣₁
        Iso.rightInv ∥∥-IdempotentR-⊎-Iso x = squash₁ (Iso.fun ∥∥-IdempotentR-⊎-Iso (Iso.inv ∥∥-IdempotentR-⊎-Iso x)) x
        Iso.leftInv ∥∥-IdempotentR-⊎-Iso x  = squash₁ (Iso.inv ∥∥-IdempotentR-⊎-Iso (Iso.fun ∥∥-IdempotentR-⊎-Iso x)) x

∥∥-IdempotentR-⊎ : ∥ A ⊎ ∥ A′ ∥₁ ∥₁ ≡ ∥ A ⊎ A′ ∥₁
∥∥-IdempotentR-⊎ = ua ∥∥-IdempotentR-⊎-≃

∥∥-Idempotent-⊎ : {A : Type ℓ} {A′ : Type ℓ'} → ∥ ∥ A ∥₁ ⊎ ∥ A′ ∥₁ ∥₁ ≡ ∥ A ⊎ A′ ∥₁
∥∥-Idempotent-⊎ {A = A} {A′} = ∥ ∥ A ∥₁ ⊎ ∥ A′ ∥₁ ∥₁ ≡⟨ ∥∥-IdempotentR-⊎ ⟩
                               ∥ ∥ A ∥₁ ⊎ A′ ∥₁     ≡⟨ ∥∥-IdempotentL-⊎ ⟩
                               ∥ A ⊎ A′ ∥₁         ∎

∥∥-IdempotentL-×-≃ : ∥ ∥ A ∥₁ × A′ ∥₁ ≃ ∥ A × A′ ∥₁
∥∥-IdempotentL-×-≃ = isoToEquiv ∥∥-IdempotentL-×-Iso
  where ∥∥-IdempotentL-×-Iso : Iso (∥ ∥ A ∥₁ × A′ ∥₁) (∥ A × A′ ∥₁)
        Iso.fun ∥∥-IdempotentL-×-Iso x = rec squash₁ lem x
          where lem : ∥ A ∥₁ × A′ → ∥ A × A′ ∥₁
                lem (a , a′) = map2 (λ a a′ → a , a′) a ∣ a′ ∣₁
        Iso.inv ∥∥-IdempotentL-×-Iso x = map lem x
          where lem : A × A′ → ∥ A ∥₁ × A′
                lem (a , a′) = ∣ a ∣₁ , a′
        Iso.rightInv ∥∥-IdempotentL-×-Iso x = squash₁ (Iso.fun ∥∥-IdempotentL-×-Iso (Iso.inv ∥∥-IdempotentL-×-Iso x)) x
        Iso.leftInv ∥∥-IdempotentL-×-Iso x  = squash₁ (Iso.inv ∥∥-IdempotentL-×-Iso (Iso.fun ∥∥-IdempotentL-×-Iso x)) x

∥∥-IdempotentL-× : ∥ ∥ A ∥₁ × A′ ∥₁ ≡ ∥ A × A′ ∥₁
∥∥-IdempotentL-× = ua ∥∥-IdempotentL-×-≃

∥∥-IdempotentR-×-≃ : ∥ A × ∥ A′ ∥₁ ∥₁ ≃ ∥ A × A′ ∥₁
∥∥-IdempotentR-×-≃ = isoToEquiv ∥∥-IdempotentR-×-Iso
  where ∥∥-IdempotentR-×-Iso : Iso (∥ A × ∥ A′ ∥₁ ∥₁) (∥ A × A′ ∥₁)
        Iso.fun ∥∥-IdempotentR-×-Iso x = rec squash₁ lem x
          where lem : A × ∥ A′ ∥₁ → ∥ A × A′ ∥₁
                lem (a , a′) = map2 (λ a a′ → a , a′) ∣ a ∣₁ a′
        Iso.inv ∥∥-IdempotentR-×-Iso x = map lem x
          where lem : A × A′ → A × ∥ A′ ∥₁
                lem (a , a′) = a , ∣ a′ ∣₁
        Iso.rightInv ∥∥-IdempotentR-×-Iso x = squash₁ (Iso.fun ∥∥-IdempotentR-×-Iso (Iso.inv ∥∥-IdempotentR-×-Iso x)) x
        Iso.leftInv ∥∥-IdempotentR-×-Iso x  = squash₁ (Iso.inv ∥∥-IdempotentR-×-Iso (Iso.fun ∥∥-IdempotentR-×-Iso x)) x

∥∥-IdempotentR-× : ∥ A × ∥ A′ ∥₁ ∥₁ ≡ ∥ A × A′ ∥₁
∥∥-IdempotentR-× = ua ∥∥-IdempotentR-×-≃

∥∥-Idempotent-× : {A : Type ℓ} {A′ : Type ℓ'} → ∥ ∥ A ∥₁ × ∥ A′ ∥₁ ∥₁ ≡ ∥ A × A′ ∥₁
∥∥-Idempotent-× {A = A} {A′} = ∥ ∥ A ∥₁ × ∥ A′ ∥₁ ∥₁ ≡⟨ ∥∥-IdempotentR-× ⟩
                               ∥ ∥ A ∥₁ × A′ ∥₁     ≡⟨ ∥∥-IdempotentL-× ⟩
                               ∥ A × A′ ∥₁         ∎

∥∥-Idempotent-×-≃ : {A : Type ℓ} {A′ : Type ℓ'} → ∥ ∥ A ∥₁ × ∥ A′ ∥₁ ∥₁ ≃ ∥ A × A′ ∥₁
∥∥-Idempotent-×-≃ {A = A} {A′} = compEquiv ∥∥-IdempotentR-×-≃ ∥∥-IdempotentL-×-≃

∥∥-×-≃ : {A : Type ℓ} {A′ : Type ℓ'} → ∥ A ∥₁ × ∥ A′ ∥₁ ≃ ∥ A × A′ ∥₁
∥∥-×-≃ {A = A} {A′} = compEquiv (invEquiv (propTruncIdempotent≃ (isProp× isPropPropTrunc isPropPropTrunc))) ∥∥-Idempotent-×-≃

∥∥-× : {A : Type ℓ} {A′ : Type ℓ'} → ∥ A ∥₁ × ∥ A′ ∥₁ ≡ ∥ A × A′ ∥₁
∥∥-× = ua ∥∥-×-≃

-- using this we get a convenient recursor/eliminator for binary functions into sets
rec2→Set : {A B C : Type ℓ} (Cset : isSet C)
         → (f : A → B → C)
         → (∀ (a a' : A) (b b' : B) → f a b ≡ f a' b')
         → ∥ A ∥₁ → ∥ B ∥₁ → C
rec2→Set {A = A} {B = B} {C = C} Cset f fconst = curry (g ∘ ∥∥-×-≃ .fst)
 where
 g : ∥ A × B ∥₁ → C
 g = rec→Set Cset (uncurry f) λ x y → fconst (fst x) (fst y) (snd x) (snd y)

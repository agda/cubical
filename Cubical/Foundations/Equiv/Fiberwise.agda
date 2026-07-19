module Cubical.Foundations.Equiv.Fiberwise where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

private
  variable
    ℓ ℓ' ℓ'' : Level

module _ {A : Type ℓ} (P : A → Type ℓ') (Q : A → Type ℓ'')
         (f : ∀ x → P x → Q x)
         where
  private
    total : (Σ A P) → (Σ A Q)
    total = (\ p → p .fst , f (p .fst) (p .snd))

  -- Thm 4.7.6
  fibers-total : ∀ {xv} → Iso (fiber total (xv)) (fiber (f (xv .fst)) (xv .snd))
  fibers-total {xv} = iso h g h-g g-h
   where
    h : ∀ {xv} → fiber total xv → fiber (f (xv .fst)) (xv .snd)
    h {xv} (p , eq) = J (\ xv eq → fiber (f (xv .fst)) (xv .snd)) ((p .snd) , refl) eq
    g : ∀ {xv} → fiber (f (xv .fst)) (xv .snd) → fiber total xv
    g {xv} (p , eq) = (xv .fst , p) , (\ i → _ , eq i)
    h-g : ∀ {xv} y → h {xv} (g {xv} y) ≡ y
    h-g {x , v} (p , eq) = J (λ _ eq₁ → h (g (p , eq₁)) ≡ (p , eq₁)) (JRefl (λ xv₁ eq₁ → fiber (f (xv₁ .fst)) (xv₁ .snd)) ((p , refl))) (eq)
    g-h : ∀ {xv} y → g {xv} (h {xv} y) ≡ y
    g-h {xv} ((a , p) , eq) = J (λ _ eq₁ → g (h ((a , p) , eq₁)) ≡ ((a , p) , eq₁))
                                (cong g (JRefl (λ xv₁ eq₁ → fiber (f (xv₁ .fst)) (xv₁ .snd)) (p , refl)))
                                eq
  -- Thm 4.7.7 (fiberwise equivalences)
  fiberEquiv : ([tf] : isEquiv total)
               → ∀ x → isEquiv (f x)
  fiberEquiv [tf] x .equiv-proof y = isContrRetract (fibers-total .Iso.inv) (fibers-total .Iso.fun) (fibers-total .Iso.rightInv)
                                                    ([tf] .equiv-proof (x , y))

  totalEquiv : (fx-equiv : ∀ x → isEquiv (f x))
               → isEquiv total
  totalEquiv fx-equiv .equiv-proof (x , v) = isContrRetract (fibers-total .Iso.fun) (fibers-total .Iso.inv) (fibers-total .Iso.leftInv)
                                                            (fx-equiv x .equiv-proof v)


module _ {U : Type ℓ} (_~_ : U → U → Type ℓ')
         (idTo~ : ∀ {A B} → A ≡ B → A ~ B)
         (c : ∀ A → ∃![ X ∈ U ] (A ~ X))
       where

  isContrToUniv : ∀ {A B} → isEquiv (idTo~ {A} {B})
  isContrToUniv {A} {B}
    = fiberEquiv (λ z → A ≡ z) (λ z → A ~ z) (\ B → idTo~ {A} {B})
                 (λ { .equiv-proof y
                    → isContrΣ (isContrSingl _)
                                   \ a → isContr→isContrPath (c A) _ _
                    })
                 B


{-
  The following is called fundamental theorem of identity types in Egbert Rijke's
  introduction to homotopy type theory.
-}
recognizeId : {A : Type ℓ} {a : A} (Eq : A → Type ℓ')
  → Eq a
  → isContr (Σ _ Eq)
  → (x : A) → (a ≡ x) ≃ (Eq x)
recognizeId {A = A} {a = a} Eq eqRefl eqContr x = (fiberMap x) , (isEquivFiberMap x)
  where
    fiberMap : (x : A) → a ≡ x → Eq x
    fiberMap x = J (λ x p → Eq x) eqRefl

    mapOnSigma : Σ[ x ∈ A ] a ≡ x → Σ _ Eq
    mapOnSigma pair = fst pair , fiberMap (fst pair) (snd pair)

    equivOnSigma : (x : A) → isEquiv mapOnSigma
    equivOnSigma x = isEquivFromIsContr mapOnSigma (isContrSingl a) eqContr

    isEquivFiberMap : (x : A) → isEquiv (fiberMap x)
    isEquivFiberMap = fiberEquiv (λ x → a ≡ x) Eq fiberMap (equivOnSigma x)

fundamentalTheoremOfId : {A : Type ℓ} (Eq : A → A → Type ℓ')
  → ((x : A) → Eq x x)
  → ((x : A) → isContr (Σ[ y ∈ A ] Eq x y))
  → (x y : A) → (x ≡ y) ≃ (Eq x y)
fundamentalTheoremOfId Eq eqRefl eqContr x = recognizeId (Eq x) (eqRefl x) (eqContr x)

fundamentalTheoremOfIdβ :
  {A : Type ℓ} (Eq : A → A → Type ℓ')
  → (eqRefl : (x : A) → Eq x x)
  → (eqContr : (x : A) → isContr (Σ[ y ∈ A ] Eq x y))
  → (x : A)
  → fst (fundamentalTheoremOfId Eq eqRefl eqContr x x) refl ≡ eqRefl x
fundamentalTheoremOfIdβ Eq eqRefl eqContr x = JRefl (λ y p → Eq x y) (eqRefl x)

{-# OPTIONS --cubical --safe #-}
module Cubical.Structures.InftyMagma where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.Foundations.SIP renaming (SNS₂ to SNS)

private
  variable
    ℓ ℓ' ℓ'' : Level

-- ∞-Magmas with SNS

-- We need function extensionality for binary functions.
-- TODO: upstream
funExtBin : {A : Type ℓ} {B : A → Type ℓ'} {C : (x : A) → B x → Type ℓ''} {f g : (x : A) → (y : B x) → C x y}
           → ((x : A) (y : B x) → f x y ≡ g x y) → f ≡ g
funExtBin p i x y = p x y i
module _ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : A → Type ℓ'} {C : (x : A) → B x → Type ℓ''} {f g : (x : A) → (y : B x) → C x y} where
  private
    appl₂ : f ≡ g → ∀ x y → f x y ≡ g x y
    appl₂ eq x y i = eq i x y

    fib : (p : f ≡ g) → fiber funExtBin p
    fib p = (appl₂ p , refl)

    funExtBin-fiber-isContr
      : (p : f ≡ g)
      → (fi : fiber funExtBin p)
      → fib p ≡ fi
    funExtBin-fiber-isContr p (h , eq) i = (appl₂ (eq (~ i)) , λ j → eq (~ i ∨ j))

  funExtBin-isEquiv : isEquiv funExtBin
  equiv-proof funExtBin-isEquiv p = (fib p , funExtBin-fiber-isContr p)

  funExtBinEquiv : (∀ x y → f x y ≡ g x y) ≃ (f ≡ g)
  funExtBinEquiv = (funExtBin , funExtBin-isEquiv)

-- ∞-Magmas
∞-magma-structure : Type ℓ → Type ℓ
∞-magma-structure X = X → X → X

∞-Magma : Type (ℓ-suc ℓ)
∞-Magma {ℓ} = TypeWithStr ℓ ∞-magma-structure

∞-magma-iso : StrIso ∞-magma-structure ℓ
∞-magma-iso (X , _·_) (Y , _∗_) f = (x x' : X) → equivFun f (x · x') ≡ (equivFun f x) ∗ (equivFun f x')

∞-magma-is-SNS : SNS {ℓ} ∞-magma-structure ∞-magma-iso
∞-magma-is-SNS (X , _·_) (Y , _∗_) f = SNS₁→SNS₂ ∞-magma-structure ∞-magma-iso C (X , _·_) (Y , _∗_) f
 where
  C : {X : Type ℓ} (_·_ _∗_ : X → X → X) → (_·_ ≡ _∗_) ≃ ((x x' : X) → (x · x') ≡ (x ∗ x'))
  C _·_ _∗_ = invEquiv funExtBinEquiv

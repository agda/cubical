{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Foundations.Pointed.Homotopy2 where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Fiberwise
open import Cubical.Foundations.Path
open import Cubical.Foundations.Transport

open import Cubical.Foundations.Pointed.Base
open import Cubical.Foundations.Pointed.Properties

open import Cubical.Homotopy.Base

open import Cubical.Data.Sigma

module SquarePath where
  module _ {ℓ : Level} {A : Type ℓ} where
    SquareTransf1 : {a₀₀ a₀₁ a₁₀ a₁₁ : A}
                    (a₀₋ : a₀₀ ≡ a₀₁)
                    (a₁₋ : a₁₀ ≡ a₁₁)
                    -- (a₋₀ : a₀₀ ≡ a₁₀)
                    -- (a₋₁ : a₀₁ ≡ a₁₁)
                    → Square a₀₋ a₁₋ refl refl ≡ Square ? ? ? ?
    SquareTransf1 = ?


-- pointed homotopies
module _ {ℓ ℓ'} {A : Pointed ℓ} {B : typ A → Type ℓ'} {ptB : B (pt A)} where

  ⋆ = pt A

  -- pointed homotopy as pointed Π
  _∙∼_ : (f g : Π∙ A B ptB) → Type (ℓ-max ℓ ℓ')
  f ∙∼ g = Π∙ A (λ x → fst f x ≡ g .fst x) (snd f ∙ (snd g) ⁻¹)

  -- pointed homotopy with PathP
  _∙∼P_ : (f g : Π∙ A B ptB) → Type (ℓ-max ℓ ℓ')
  f ∙∼P g = Σ[ h ∈ (fst f) ∼ (fst g) ]
               PathP (λ i → h (pt A) i ≡ ptB) (snd f) (snd g)

  module _ {f g : Π∙ A B ptB} where
    private
      f₁ = fst f
      f₂ = snd f
      g₁ = fst g
      g₂ = snd g
             
    P : (H : f₁ ∼ g₁) → Type ℓ'
    P H = H ⋆ ≡ f₂ ∙ g₂ ⁻¹
                        
    Q : (H : f₁ ∼ g₁) → Type ℓ'
    Q H = PathP (λ i → H ⋆ i ≡ ptB) f₂ g₂

    φ : (H : f₁ ∼ g₁) → P H → Q H
    φ H = {!!}

  module _ (f g : Π∙ A B ptB) where
    private
      f₁ = fst f
      f₂ = snd f
      g₁ = fst g
      g₂ = snd g

    _∙∼Σ_ = Σ[ H ∈ f₁ ∼ g₁ ] (P {f = f} {g = g} H)
    _∙∼PΣ_ = Σ[ H ∈ f₁ ∼ g₁ ] (Q {f = f} {g = g} H)

  ∙∼≡∙∼Σ : (f g : Π∙ A B ptB) → f ∙∼ g ≡ f ∙∼Σ g
  ∙∼≡∙∼Σ f g = refl

  ∙∼P≡∙∼PΣ : (f g : Π∙ A B ptB) → f ∙∼P g ≡ f ∙∼PΣ g
  ∙∼P≡∙∼PΣ f g = refl

  totφ : {f g : Π∙ A B ptB} → f ∙∼Σ g → f ∙∼PΣ g
  totφ {f = f} {g = g} (p₁ , p₂) = p₁ , φ {f = f} {g = g} p₁ p₂

  ∙∼≃∙∼P : (f g : Π∙ A B ptB) → (f ∙∼Σ g) ≃ (f ∙∼PΣ g)
  ∙∼≃∙∼P f g = totφ {f = f} {g = g} , totalEquiv (P {f = f} {g = g})
                                                    (Q {f = f} {g = g})
                                                    (φ {f = f} {g = g})
                                                    {!!}



  -- the two kinds of homotopies are equivalent

  -- ∙∼Iso : (f g : Π∙ A B ptB) → (f ∙∼ g) ≃ (f ∙∼P g)
  -- ∙∼Iso f g = {!!} , (totalEquiv {!!} {!!} {!!} {!!})

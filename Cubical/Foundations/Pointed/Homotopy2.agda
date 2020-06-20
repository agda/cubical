{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Foundations.Pointed.Homotopy2 where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Fiberwise
open import Cubical.Foundations.Path
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Pointed.Base
open import Cubical.Foundations.Pointed.Properties

open import Cubical.Homotopy.Base

open import Cubical.Data.Sigma

module _ {ℓ : Level} {A : Type ℓ} {a₀₀ a₀₁ a₁₀ a₁₁ : A} where
  Square≃doubleComp : (a₀₋ : a₀₀ ≡ a₀₁)
                      (a₁₋ : a₁₀ ≡ a₁₁)
                      (a₋₀ : a₀₀ ≡ a₁₀)
                      (a₋₁ : a₀₁ ≡ a₁₁)
                      → Square a₀₋ a₁₋ a₋₀ a₋₁ ≃ (a₋₀ ⁻¹ ∙∙ a₀₋ ∙∙ a₋₁ ≡ a₁₋)
  Square≃doubleComp a₀₋ a₁₋ a₋₀ a₋₁ = transportEquiv (PathP≡doubleCompPathˡ a₋₀ a₀₋ a₁₋ a₋₁)


module _ {ℓ : Level}  where
  symIso : {A : Type ℓ} {a b : A} (p q : a ≡ b) → Iso (p ≡ q) (q ≡ p)
  symIso p q = iso sym sym (λ _ → refl) λ _ → refl

  open import Cubical.Foundations.Equiv.HalfAdjoint
  compr≡Equiv : {A : Type ℓ} {a b c : A} (p q : a ≡ b) (r : b ≡ c) → (p ≡ q) ≃ (p ∙ r ≡ q ∙ r)
  compr≡Equiv p q r = congEquiv ((λ s → s ∙ r) , compPathr-isEquiv r)

  compl≡Equiv : {A : Type ℓ} {a b c : A} (p : a ≡ b) (q r : b ≡ c) → (q ≡ r) ≃ (p ∙ q ≡ p ∙ r)
  compl≡Equiv p q r = congEquiv ((λ s → p ∙ s) , (compPathl-isEquiv p))

  -- cong≡ : {A : Type ℓ} {a b c : A} (p : a ≡ b) → (a ≡ c) ≡ (b ≡ c)
  -- cong≡ {c = c} = cong (_≡ c)

{-
    lWhisker : {A : Type ℓ} {a b c : A} (p : a ≡ b) (q r : b ≡ c) (H : q ≡ r) → p ∙ q ≡ p ∙ r
    lWhisker p q r H = λ i → p ∙ (H i)
?3 : (a ≡ b) ≃ (a ≡ c)

    lWhiskerIso : {A : Type ℓ} {a b c : A} (p : a ≡ b) (q r : b ≡ c) → Iso (q ≡ r) (p ∙ q ≡ p ∙ r)
    lWhiskerIso p q r = iso (lWhisker p q r)
                            (λ H i → {!!})
                            {!!} {!!}

    lWhisker≡ : {A : Type ℓ} {a b c : A} (p : a ≡ b) (q r : b ≡ c) → (q ≡ r) ≡ (p ∙ q ≡ p ∙ r)
    lWhisker≡ p q r = {!!}

    lInv≡ : {A : Type ℓ} {a b c : A} (p : a ≡ b) (q : b ≡ c) (r : a ≡ c) → (p ∙ q ≡ r) ≡ (q ≡ p ⁻¹ ∙ r)
    lInv≡ p q r = (lWhisker≡ (p ⁻¹) (p ∙ q) r) ∙ (cong≡ (assoc (p ⁻¹) p q ∙∙ cong (_∙ q) (lCancel p) ∙∙ sym (lUnit q)))
    -}

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


  module _ {f g : Π∙ A B ptB} (H : f .fst ∼ g .fst) where
    private
      f₁ = fst f
      f₂ = snd f
      g₁ = fst g
      g₂ = snd g
             
    P : Type ℓ'
    P = H ⋆ ≡ f₂ ∙ g₂ ⁻¹
                        
    Q : Type ℓ'
    Q = PathP (λ i → H ⋆ i ≡ ptB) f₂ g₂

    p = H ⋆
    r = f₂
    s = g₂
    P≡Q : P ≡ Q
    P≡Q = p ≡ r ∙ s ⁻¹ ≡⟨ isoToPath (symIso p (r ∙ s ⁻¹)) ⟩
          r ∙ s ⁻¹ ≡ p
            ≡⟨ cong (r ∙ s ⁻¹ ≡_) (rUnit p ∙∙ cong (p ∙_) (sym (rCancel s)) ∙∙ assoc p s (s ⁻¹)) ⟩
          r ∙ s ⁻¹ ≡ (p ∙ s) ∙ s ⁻¹
            ≡⟨ sym (ua (compr≡Equiv r (p ∙ s) (s ⁻¹))) ⟩
          r ≡ p ∙ s
            ≡⟨ ua (compl≡Equiv (p ⁻¹) r (p ∙ s)) ⟩
          p ⁻¹ ∙ r ≡ p ⁻¹ ∙ (p ∙ s)
            ≡⟨ cong (p ⁻¹ ∙ r ≡_ ) (assoc (p ⁻¹) p s ∙∙ (cong (_∙ s) (lCancel p)) ∙∙ sym (lUnit s)) ⟩
          p ⁻¹ ∙ r ≡ s
            ≡⟨ cong (λ z → p ⁻¹ ∙ z ≡ s) (rUnit r) ⟩
          p ⁻¹ ∙ (r ∙ refl) ≡ s
            ≡⟨ cong (_≡ s) (sym (doubleCompPath-elim' (p ⁻¹) r refl)) ⟩
          p ⁻¹ ∙∙ r ∙∙ refl ≡ s
            ≡⟨ sym (ua (Square≃doubleComp r s p refl)) ⟩
          PathP (λ i → p i ≡ ptB) r s ∎


    φ : P → Q
    φ = transport P≡Q


  _∙∼Σ_ : (f g : Π∙ A B ptB) → Type (ℓ-max ℓ ℓ')
  f ∙∼Σ g = Σ[ H ∈ f .fst ∼ g .fst ] (P {f = f} {g = g} H)

  _∙∼PΣ_ : (f g : Π∙ A B ptB) → Type (ℓ-max ℓ ℓ')
  f ∙∼PΣ g = Σ[ H ∈ f .fst ∼ g .fst ] (Q {f = f} {g = g} H)

  ∙∼≡∙∼Σ : (f g : Π∙ A B ptB) → f ∙∼ g ≡ f ∙∼Σ g
  ∙∼≡∙∼Σ f g = refl

  ∙∼P≡∙∼PΣ : (f g : Π∙ A B ptB) → f ∙∼P g ≡ f ∙∼PΣ g
  ∙∼P≡∙∼PΣ f g = refl

  totφ : {f g : Π∙ A B ptB} → f ∙∼Σ g → f ∙∼PΣ g
  totφ {f = f} {g = g} (p₁ , p₂) = p₁ , φ {f = f} {g = g} p₁ p₂

{-
  ∙∼≃∙∼P : (f g : Π∙ A B ptB) → (f ∙∼Σ g) ≃ (f ∙∼PΣ g)
  ∙∼≃∙∼P f g = totφ {f = f} {g = g} , totalEquiv (P {f = f} {g = g})
                                                    (Q {f = f} {g = g})
                                                    (φ {f = f} {g = g})
                                                    λ H → isEquivTransport (P≡Q H)

-}


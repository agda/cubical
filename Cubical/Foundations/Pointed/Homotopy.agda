module Cubical.Foundations.Pointed.Homotopy where

{-
  This module defines two kinds of pointed homotopies,
  ∙∼ and ∙∼P, and proves their equivalence
-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Fiberwise
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Path
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Pointed.Base
open import Cubical.Foundations.Pointed.Properties
open import Cubical.Homotopy.Base
open import Cubical.Data.Sigma

private
  variable
    ℓ ℓ' : Level

module _ {A : Pointed ℓ} {B : typ A → Type ℓ'} {ptB : B (pt A)} where

  ⋆ = pt A

  -- pointed homotopy as pointed Π. This is just a Σ-type, see ∙∼Σ
  _∙∼_ : (f g : Π∙ A B ptB) → Type (ℓ-max ℓ ℓ')
  (f₁ , f₂) ∙∼ (g₁ , g₂) = Π∙ A (λ x → f₁ x ≡ g₁ x) (f₂ ∙ g₂ ⁻¹)

  -- pointed homotopy with PathP. Also a Σ-type, see ∙∼PΣ
  _∙∼P_ : (f g : Π∙ A B ptB) → Type (ℓ-max ℓ ℓ')
  (f₁ , f₂) ∙∼P (g₁ , g₂) = Σ[ h ∈ f₁ ∼ g₁ ] PathP (λ i → h ⋆ i ≡ ptB) f₂ g₂

  -- Proof that f ∙∼ g ≃ f ∙∼P g
  -- using equivalence of the total map of φ
  private
    module _ (f g : Π∙ A B ptB) (H : f .fst ∼ g .fst) where
      -- convenient notation
      f₁ = fst f
      f₂ = snd f
      g₁ = fst g
      g₂ = snd g

      -- P is the predicate on a homotopy H to be pointed of the ∙∼ kind
      P : Type ℓ'
      P = H ⋆ ≡ f₂ ∙ g₂ ⁻¹

      -- Q is the predicate on a homotopy H to be pointed of the ∙∼P kind
      Q : Type ℓ'
      Q = PathP (λ i → H ⋆ i ≡ ptB) f₂ g₂

      -- simplify the notation even more to see that P≡Q
      -- is just a jingle of paths
      p = H ⋆
      r = f₂
      s = g₂
      P≡Q : P ≡ Q
      P≡Q = p ≡ r ∙ s ⁻¹
              ≡⟨ isoToPath symIso ⟩
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

      -- φ is a fiberwise transformation (H : f ∼ g) → P H → Q H
      -- φ is even a fiberwise equivalence by P≡Q
      φ : P → Q
      φ = transport P≡Q

    -- The total map corresponding to φ
    totφ : (f g : Π∙ A B ptB) → f ∙∼ g → f ∙∼P g
    totφ f g p .fst = p .fst
    totφ f g p .snd = φ f g (p .fst) (p .snd)

  -- transformation of the homotopies using totφ
  ∙∼→∙∼P : (f g : Π∙ A B ptB) → (f ∙∼ g) → (f ∙∼P g)
  ∙∼→∙∼P f g = totφ f g

  -- Proof that ∙∼ and ∙∼P are equivalent using the fiberwise equivalence φ
  ∙∼≃∙∼P : (f g : Π∙ A B ptB) → (f ∙∼ g) ≃ (f ∙∼P g)
  ∙∼≃∙∼P f g = Σ-cong-equiv-snd (λ H → pathToEquiv (P≡Q f g H))

  -- inverse of ∙∼→∙∼P extracted from the equivalence
  ∙∼P→∙∼ : {f g : Π∙ A B ptB} → f ∙∼P g → f ∙∼ g
  ∙∼P→∙∼ {f = f} {g = g} = invEq (∙∼≃∙∼P f g)

  -- ∙∼≃∙∼P transformed to a path
  ∙∼≡∙∼P : (f g : Π∙ A B ptB) → (f ∙∼ g) ≡ (f ∙∼P g)
  ∙∼≡∙∼P f g = ua (∙∼≃∙∼P f g)

  -- Verifies that the pointed homotopies actually correspond
  -- to their Σ-type versions
  _∙∼Σ_ : (f g : Π∙ A B ptB) → Type (ℓ-max ℓ ℓ')
  f ∙∼Σ g = Σ[ H ∈ f .fst ∼ g .fst ] (P f g H)

  _∙∼PΣ_ : (f g : Π∙ A B ptB) → Type (ℓ-max ℓ ℓ')
  f ∙∼PΣ g = Σ[ H ∈ f .fst ∼ g .fst ] (Q f g H)

  ∙∼≡∙∼Σ : (f g : Π∙ A B ptB) → f ∙∼ g ≡ f ∙∼Σ g
  ∙∼≡∙∼Σ f g = refl

  ∙∼P≡∙∼PΣ : (f g : Π∙ A B ptB) → f ∙∼P g ≡ f ∙∼PΣ g
  ∙∼P≡∙∼PΣ f g = refl

module Cubical.Data.IterativeMultisets.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Fiberwise
open import Cubical.Foundations.HLevels
open import Cubical.Functions.Embedding
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Sigma

open import Cubical.Data.IterativeMultisets.Base

private
  variable
    ℓ : Level

private
  ≡V∞-≃-≡lift-V∞ : (ℓ' : Level) (x y : V∞ {ℓ}) → (x ≡ y) ≃ (lift-V∞ ℓ' x ≡ lift-V∞ ℓ' y)
  ≡V∞-≃-≡lift-V∞ {ℓ} ℓ' (sup-∞ A α) (sup-∞ B β) =
    (sup-∞ A α ≡ sup-∞ B β)
      ≃⟨ ≡V∞-≃-≡Equiv ⟩
    (Σ[ e ∈ A ≃ B ] α ≡ β ∘ e .fst)
      ≃⟨ Σ-cong-equiv Lift≃ elements≃ ⟩
    (Σ[ e ∈ Lift ℓ' A ≃ Lift ℓ' B ] α' ≡ β' ∘ e .fst)
      ≃⟨ invEquiv ≡V∞-≃-≡Equiv ⟩
    (lift-V∞ ℓ' (sup-∞ A α) ≡ lift-V∞ ℓ' (sup-∞ B β)) ■
    where
      α' : Lift ℓ' A → V∞ {ℓ-max ℓ ℓ'}
      α' a = lift-V∞ ℓ' (α (a .lower))

      β' : Lift ℓ' B → V∞ {ℓ-max ℓ ℓ'}
      β' b = lift-V∞ ℓ' (β (b .lower))

      Lift≃ : (A ≃ B) ≃ (Lift ℓ' A ≃ Lift ℓ' B)
      Lift≃ = equivComp LiftEquiv LiftEquiv

      elements≃ : (e : A ≃ B) → (α ≡ β ∘ e .fst) ≃ (α' ≡ β' ∘ Lift≃ .fst e .fst)
      elements≃ e =
        (α ≡ β ∘ e .fst)
          ≃⟨ invEquiv funExtEquiv ⟩
        ((a : A) → α a ≡ β (e .fst a))
          ≃⟨ equivΠ LiftEquiv (λ a → ≡V∞-≃-≡lift-V∞ ℓ' (α a) (β (e .fst a))) ⟩
        ((a : Lift ℓ' A) → α' a ≡ β' (Lift≃ .fst e .fst a))
          ≃⟨ funExtEquiv ⟩
        (α' ≡ β' ∘ Lift≃ .fst e .fst) ■

lift-V∞-inj : (ℓ' : Level) (x y : V∞ {ℓ}) → lift-V∞ ℓ' x ≡ lift-V∞ ℓ' y → x ≡ y
lift-V∞-inj ℓ' x y = invEq (≡V∞-≃-≡lift-V∞ ℓ' x y)

isEmbedding-lift-V∞ : (ℓ' : Level) → isEmbedding (lift-V∞ {ℓ} ℓ')
isEmbedding-lift-V∞ {ℓ} ℓ' x y =
  isContrToUniv (λ x y → lift-V∞ ℓ' x ≡ lift-V∞ ℓ' y) (cong (lift-V∞ ℓ')) isContrTotal
  where
    isContrTotal : (x : V∞ {ℓ}) → isContr (Σ[ y ∈ V∞ {ℓ} ] lift-V∞ ℓ' x ≡ lift-V∞ ℓ' y)
    isContrTotal x =
      isOfHLevelRespectEquiv 0 (Σ-cong-equiv-snd (≡V∞-≃-≡lift-V∞ ℓ' x)) (isContrSingl x)

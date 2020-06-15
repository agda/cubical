{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Data.HomotopyGroup.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
import Cubical.Foundations.GroupoidLaws as GL
open import Cubical.Foundations.Pointed

open import Cubical.Data.Nat
open import Cubical.Data.Group.Base

open import Cubical.Homotopy.Loopspace

open import Cubical.HITs.SetTruncation as SetTrunc

π^_ : ∀ {ℓ} → ℕ → Pointed ℓ → Group ℓ
π^_ {ℓ} n p = group ∥ A ∥₂  squash₂ g
  where
    n' : ℕ
    n' = suc n

    A : Type ℓ
    A = typ ((Ω^ n') p)

    g : isGroup ∥ A ∥₂
    g = group-struct e _⁻¹ _⊙_ lUnit rUnit assoc lCancel rCancel
      where
        e : ∥ A ∥₂
        e = ∣ pt ((Ω^ n') p) ∣₂

        _⁻¹ : ∥ A ∥₂ → ∥ A ∥₂
        _⁻¹ = SetTrunc.elim {B = λ _ → ∥ A ∥₂} (λ x → squash₂) λ a → ∣  sym a ∣₂

        _⊙_ : ∥ A ∥₂ → ∥ A ∥₂ → ∥ A ∥₂
        _⊙_ = SetTrunc.elim2 (λ _ _ → squash₂) λ a₀ a₁ → ∣ a₀ ∙ a₁ ∣₂

        lUnit : (a : ∥ A ∥₂) → (e ⊙ a) ≡ a
        lUnit = SetTrunc.elim (λ _ → isProp→isSet (squash₂ _ _))
                (λ a → cong ∣_∣₂ (sym (GL.lUnit a) ))

        rUnit : (a : ∥ A ∥₂) → a ⊙ e ≡ a
        rUnit = SetTrunc.elim (λ _ → isProp→isSet (squash₂ _ _))
                (λ a → cong ∣_∣₂ (sym (GL.rUnit a) ))

        assoc : (a b c : ∥ A ∥₂) → ((a ⊙ b) ⊙ c) ≡ (a ⊙ (b ⊙ c))
        assoc = SetTrunc.elim3 (λ _ _ _ → isProp→isSet (squash₂ _ _))
                (λ a b c → cong ∣_∣₂ (sym (GL.assoc _ _ _)))

        lCancel : (a : ∥ A ∥₂) → ((a ⁻¹) ⊙ a) ≡ e
        lCancel = SetTrunc.elim (λ _ → isProp→isSet (squash₂ _ _))
                  λ a → cong ∣_∣₂ (GL.lCancel _)

        rCancel : (a : ∥ A ∥₂) → (a ⊙ (a ⁻¹)) ≡ e
        rCancel = SetTrunc.elim (λ _ → isProp→isSet (squash₂ _ _))
                  λ a → cong ∣_∣₂ (GL.rCancel _)

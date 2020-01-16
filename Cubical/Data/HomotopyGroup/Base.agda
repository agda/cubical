{-# OPTIONS --cubical --safe #-}
module Cubical.Data.HomotopyGroup.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
import Cubical.Foundations.GroupoidLaws as GL
open import Cubical.Foundations.Pointed

open import Cubical.Data.Nat
open import Cubical.Data.Group.Base

open import Cubical.HITs.SetTruncation

Ω : ∀ {ℓ} → Pointed ℓ → Pointed ℓ
Ω (A , a ) = ( (a ≡ a) , refl)

Ω^_ : ∀ {ℓ} → ℕ → Pointed ℓ → Pointed ℓ
(Ω^ 0) p = p
(Ω^ (suc n)) p = Ω ((Ω^ n) p)

π^_ : ∀ {ℓ} → ℕ → Pointed ℓ → Group ℓ
π^_ {ℓ} n p = group ∥ A ∥₀  squash₀ g
  where
    n' : ℕ
    n' = suc n

    A : Type ℓ
    A = typ ((Ω^ n') p)

    g : isGroup ∥ A ∥₀
    g = group-struct e _⁻¹ _⊙_ lUnit rUnit assoc lCancel rCancel
      where
        e : ∥ A ∥₀
        e = ∣ pt ((Ω^ n') p) ∣₀

        _⁻¹ : ∥ A ∥₀ → ∥ A ∥₀
        _⁻¹ = elimSetTrunc {B = λ _ → ∥ A ∥₀} (λ x → squash₀) λ a → ∣  sym a ∣₀

        _⊙_ : ∥ A ∥₀ → ∥ A ∥₀ → ∥ A ∥₀
        _⊙_ = elimSetTrunc2 (λ _ _ → squash₀) λ a₀ a₁ → ∣ a₀ ∙ a₁ ∣₀

        lUnit : (a : ∥ A ∥₀) → (e ⊙ a) ≡ a
        lUnit = elimSetTrunc (λ _ → isProp→isSet (squash₀ _ _))
                (λ a → cong ∣_∣₀ (sym (GL.lUnit a) ))

        rUnit : (a : ∥ A ∥₀) → a ⊙ e ≡ a
        rUnit = elimSetTrunc (λ _ → isProp→isSet (squash₀ _ _))
                (λ a → cong ∣_∣₀ (sym (GL.rUnit a) ))

        assoc : (a b c : ∥ A ∥₀) → ((a ⊙ b) ⊙ c) ≡ (a ⊙ (b ⊙ c))
        assoc = elimSetTrunc3 (λ _ _ _ → isProp→isSet (squash₀ _ _))
                (λ a b c → cong ∣_∣₀ (sym (GL.assoc _ _ _)))

        lCancel : (a : ∥ A ∥₀) → ((a ⁻¹) ⊙ a) ≡ e
        lCancel = elimSetTrunc (λ _ → isProp→isSet (squash₀ _ _))
                  λ a → cong ∣_∣₀ (GL.lCancel _)

        rCancel : (a : ∥ A ∥₀) → (a ⊙ (a ⁻¹)) ≡ e
        rCancel = elimSetTrunc (λ _ → isProp→isSet (squash₀ _ _))
                  λ a → cong ∣_∣₀ (GL.rCancel _)

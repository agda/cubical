{-# OPTIONS --cubical --safe #-}
module Cubical.Algebra.BasicProp where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma

open import Cubical.Structures.Group



private
  variable
    ℓ ℓ' : Level

---------------------------------------------------------------------
-- Groups basic properties
---------------------------------------------------------------------

-- We will use the multiplicative notation for groups

module _ (G : Group {ℓ}) where

  open group-·syntax G

  private
    ₁· = group-lid G

    ·₁ = group-rid G

    ·-assoc = group-assoc G

    ⁻¹· = group-linv G

    ·⁻¹ = group-rinv G

  id-is-unique : isContr (Σ[ x ∈ ⟨ G ⟩ ] ∀ (y : ⟨ G ⟩) → (x · y ≡ y) × (y · x ≡ y))
  id-is-unique = (₁ , λ y → ₁· y , ·₁ y) ,
                 λ { (e , is-unit) → Σ≡Prop (λ x → isPropΠ λ y → isPropΣ (group-is-set G _ _)
                                                                    λ _ →    group-is-set G _ _)
                                              (₁     ≡⟨ sym (snd (is-unit ₁)) ⟩
                                               ₁ · e ≡⟨ ₁· e ⟩
                                               e ∎
                                              )}

  are-inverses : ∀ (x y : ⟨ G ⟩)
               → x · y ≡ ₁
               → (y ≡ x ⁻¹) × (x ≡ y ⁻¹)
  are-inverses x y eq = (y                ≡⟨ sym (₁· y) ⟩
                         ₁ · y            ≡⟨ sym (·-assoc _ _ _ ∙ cong (_· y) (⁻¹· _)) ⟩
                         (x ⁻¹) · (x · y) ≡⟨ cong ((x ⁻¹) ·_) eq ⟩
                         (x ⁻¹) · ₁       ≡⟨ ·₁ _ ⟩
                         x ⁻¹ ∎)
                     , (x                 ≡⟨ sym (·₁ x) ⟩
                        x · ₁             ≡⟨ cong (x ·_) (sym (·⁻¹ y)) ∙ ·-assoc _ _ _ ⟩
                        (x · y) · (y ⁻¹)  ≡⟨ cong (_· (y ⁻¹)) eq ⟩
                        ₁ · (y ⁻¹)        ≡⟨ ₁· _ ⟩
                        y ⁻¹ ∎)

  inv-involutive : ∀ (x : ⟨ G ⟩)
                 → (x ⁻¹) ⁻¹ ≡ x
  inv-involutive x = sym (snd (are-inverses x (x ⁻¹) (·⁻¹ x)))

  inv-distr : ∀ (x y : ⟨ G ⟩) → (x · y) ⁻¹ ≡ (y ⁻¹) · (x ⁻¹)
  inv-distr x y = sym (fst (are-inverses _ _ γ))
    where γ : (x · y) · ((y ⁻¹) · (x ⁻¹)) ≡ ₁
          γ = (x · y) · ((y ⁻¹) · (x ⁻¹)) ≡⟨ sym (cong (x ·_) (sym (·-assoc _ _ _)) ∙ ·-assoc _ _ _) ⟩
              x · ((y · (y ⁻¹)) · (x ⁻¹)) ≡⟨ cong (λ - → x · (- · (x ⁻¹))) (·⁻¹ y) ⟩
              x · (₁ · (x ⁻¹))            ≡⟨ cong (x ·_) (₁· (x ⁻¹)) ⟩
              x · (x ⁻¹)                  ≡⟨ ·⁻¹ x ⟩
              ₁ ∎

  left-cancel : ∀ (x y z : ⟨ G ⟩) → x · y ≡ x · z → y ≡ z
  left-cancel x y z eq = y                ≡⟨ sym (cong (_· y) (⁻¹· x) ∙ ₁· y) ⟩
                         ((x ⁻¹) · x) · y ≡⟨ sym (·-assoc _ _ _) ⟩
                         (x ⁻¹) · (x · y) ≡⟨ cong ((x ⁻¹) ·_) eq ⟩
                         (x ⁻¹) · (x · z) ≡⟨ ·-assoc _ _ _ ⟩
                         ((x ⁻¹) · x) · z ≡⟨ cong (_· z) (⁻¹· x) ∙ ₁· z ⟩
                         z ∎

  right-cancel : ∀ (x y z : ⟨ G ⟩) → x · z ≡ y · z → x ≡ y
  right-cancel x y z eq = x                ≡⟨ sym (cong (x ·_) (·⁻¹ z) ∙ ·₁ x) ⟩
                          x · (z · (z ⁻¹)) ≡⟨ ·-assoc _ _ _ ⟩
                          (x · z) · (z ⁻¹) ≡⟨ cong (_· (z ⁻¹)) eq ⟩
                          (y · z) · (z ⁻¹) ≡⟨ sym (·-assoc _ _ _) ⟩
                          y · (z · (z ⁻¹)) ≡⟨ cong (y ·_) (·⁻¹ z) ∙ ·₁ y ⟩
                          y ∎

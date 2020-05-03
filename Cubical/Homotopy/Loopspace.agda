{-# OPTIONS --cubical --safe #-}

module Cubical.Homotopy.Loopspace where

open import Cubical.Core.Everything

open import Cubical.Data.Nat

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws
open import Cubical.HITs.SetTruncation

{- loop space of a pointed type -}
Ω : {ℓ : Level} → Pointed ℓ → Pointed ℓ
Ω (_ , a) = ((a ≡ a) , refl)

{- n-fold loop space of a pointed type -}
Ω^_ : ∀ {ℓ} → ℕ → Pointed ℓ → Pointed ℓ
(Ω^ 0) p = p
(Ω^ (suc n)) p = Ω ((Ω^ n) p)

{- loop space map -}
Ω→ : ∀ {ℓA ℓB} {A : Pointed ℓA} {B : Pointed ℓB} (f : A →∙ B) → (Ω A →∙ Ω B)
Ω→ (f , f∙) = (λ p → (sym f∙ ∙ cong f p) ∙ f∙) , cong (λ q → q ∙ f∙) (sym (rUnit (sym f∙))) ∙ lCancel f∙


-- Eckmann-Hilton --

{- Horizontal composition -}
_⋆_ : ∀ {ℓ} {A : Type ℓ} {a b c : A} {p q : a ≡ b} {p' q' : b ≡ c} → (p ≡ q) → (p' ≡ q')
   → p ∙ p' ≡ q ∙ q'
_⋆_ α β i = α i ∙ β i

{- Exchange law-}
exchange : ∀ {ℓ} {A : Type ℓ} {a b c : A} {p q r : a ≡ b} {p' q' r' : b ≡ c}
           (α : p ≡ q) (β : q ≡ r) (α' : p' ≡ q') (β' : q' ≡ r')
        → (α ∙ β) ⋆ (α' ∙ β') ≡ (α ⋆ α') ∙ (β ⋆ β')
exchange {A = A} {a = a} {c = c} {p = p} {r = r} {p' = p'} {r' = r'} α β α' β' z i =
  hcomp (λ k → λ { (i = i0) → p ∙ p'
                  ; (i = i1) → (β ⋆ β') (k ∨ ~ z)
                  ; (z = i0) → ((α ∙ β) ⋆ (α' ∙ β')) i })
        (bottom z i)
  where
  bottom : PathP (λ i → p ∙ p' ≡ (β ⋆ β') (~ i)) ((α ∙ β) ⋆ (α' ∙ β')) (α ⋆ α')
  bottom i =
    hcomp (λ k → λ { (i = i0) → (α ∙ β) ⋆ (α' ∙ β')
                    ; (i = i1) → rUnit α (~ k) ⋆ rUnit α' (~ k)})
          ((α ∙ λ j → β (~ i ∧ j)) ⋆ (α' ∙ λ j → β' (~ i ∧ j)))

Eckmann-Hilton : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) (α β : typ ((Ω^ (2 + n)) A))
              → α ∙ β ≡ β ∙ α
Eckmann-Hilton {A = (A , pt)} zero α β =
  α ∙ β                                                                                      ≡⟨ (λ i → unit1 α (~ i) ∙ unit2 β (~ i)) ⟩
  (rUnit refl ∙ (refl ⋆ α) ∙ sym (rUnit refl)) ∙ lUnit refl ∙ (β ⋆ refl) ∙ sym (lUnit refl)  ≡⟨ helper (rUnit refl) (refl ⋆ α) (β ⋆ refl) ⟩
  rUnit refl ∙ ((refl ⋆ α) ∙ (β ⋆ refl)) ∙ sym (rUnit refl)                                  ≡⟨ (λ i → rUnit refl ∙ exchange refl β α refl (~ i) ∙ sym (rUnit refl)) ⟩
  rUnit refl ∙ ((refl ∙ β) ⋆ (α ∙ refl)) ∙ sym (rUnit refl)                                  ≡⟨ (λ i → rUnit refl ∙ helper2 i ∙ sym (rUnit refl)) ⟩
  rUnit refl ∙ ((β ∙ refl) ⋆ (refl ∙ α)) ∙ sym (rUnit refl)                                  ≡⟨ (λ i → rUnit refl ∙ exchange β refl refl α i ∙ sym (rUnit refl) ) ⟩
  rUnit refl ∙ ((β ⋆ refl) ∙ (refl ⋆ α)) ∙ sym (rUnit refl)                                  ≡⟨ sym (helper (rUnit refl) (β ⋆ refl) (refl ⋆ α))  ⟩
  (lUnit refl ∙ (β ⋆ refl) ∙ sym (lUnit refl)) ∙ rUnit refl ∙ (refl ⋆ α) ∙ sym (rUnit refl)  ≡⟨ (λ i → unit2 β i ∙ unit1 α i) ⟩
  β ∙ α ∎
  where
  helper : ∀ {ℓ} {A : Type ℓ} {a b : A} (p : a ≡ b) (q q' : b ≡ b)
        → (p ∙ q ∙ (sym p)) ∙ p ∙ q' ∙ sym p ≡ p ∙ (q ∙ q') ∙ sym p
  helper p q q' =
    (p ∙ q ∙ (sym p)) ∙ p ∙ q' ∙ sym p                      ≡⟨ (λ i → assoc p q (sym p) i ∙ p ∙ q' ∙ sym p) ⟩
    ((p ∙ q) ∙ sym p) ∙ p ∙ q' ∙ sym p                      ≡⟨ assoc ((p ∙ q) ∙ sym p) p (q' ∙ sym p) ⟩
    (((p ∙ q) ∙ sym p) ∙ p) ∙ q' ∙ sym p                    ≡⟨ (λ i → assoc (p ∙ q) (sym p) p (~ i) ∙ q' ∙ sym p) ⟩
    ((p ∙ q) ∙ (sym p ∙ p)) ∙ q' ∙ sym p                    ≡⟨ (λ i → ((p ∙ q) ∙ lCancel p i) ∙ q' ∙ sym p) ⟩
    ((p ∙ q) ∙ refl) ∙ q' ∙ sym p                           ≡⟨ (λ i → rUnit (p ∙ q) (~ i) ∙ q' ∙ sym p) ⟩
    (p ∙ q) ∙ q' ∙ sym p                                    ≡⟨ assoc (p ∙ q) q' (sym p) ⟩
    ((p ∙ q) ∙ q') ∙ sym p                                  ≡⟨ (λ i → assoc p q q' (~ i) ∙ sym p) ⟩
    (p ∙ (q ∙ q')) ∙ sym p                                  ≡⟨ sym (assoc p (q ∙ q') (sym p)) ⟩
    p ∙ (q ∙ q') ∙ sym p ∎

  helper2 : (refl ∙ β) ⋆ (α ∙ refl) ≡ ((β ∙ refl) ⋆ (refl ∙ α))
  helper2 = (λ i → (rUnit ((lUnit β) (~ i)) i) ⋆ (lUnit (rUnit α (~ i)) i))

  unit1 : {a : A} (γ : Path (a ≡ a) (λ _ → a) λ _ → a)
       → lUnit refl ∙ (refl ⋆ γ) ∙ sym (lUnit refl) ≡ γ
  unit1 {a = a} γ = lUnit refl ∙ (refl ⋆ γ) ∙ sym (lUnit refl)  ≡⟨ (λ i → (λ j → lUnit refl (j ∧ ~ i)) ∙ (λ j → lUnit (γ j) (~ i)) ∙ λ j → lUnit refl (~ i ∧ ~ j)) ⟩
                    refl ∙ γ ∙ refl                             ≡⟨ (λ i → lUnit (rUnit γ (~ i)) (~ i)) ⟩
                    γ ∎


  unit2 : {a : A} (γ : Path (a ≡ a) (λ _ → a) λ _ → a)
       → rUnit refl ∙ (γ ⋆ refl) ∙ sym (rUnit refl) ≡ γ
  unit2 γ = rUnit refl ∙ (γ ⋆ refl) ∙ sym (rUnit refl)          ≡⟨ (λ i → (λ j → rUnit refl (j ∧ ~ i)) ∙ (λ j → rUnit (γ j) (~ i)) ∙ λ j → rUnit refl (~ i ∧ ~ j)) ⟩
            refl ∙ γ ∙ refl                                     ≡⟨ (λ i → lUnit (rUnit γ (~ i)) (~ i)) ⟩
            γ ∎

Eckmann-Hilton {A = (A , pt)} (suc n) α β = Eckmann-Hilton 0 α β


{- Homotopy group version -}
π-comp : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) → ∥ typ ((Ω^ (suc n)) A) ∥₀
      → ∥ typ ((Ω^ (suc n)) A) ∥₀ → ∥ typ ((Ω^ (suc n)) A) ∥₀
π-comp n = elim2 (λ _ _ → setTruncIsSet) λ p q → ∣ p ∙ q ∣₀

Eckmann-Hilton-π : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) (p q : ∥ typ ((Ω^ (2 + n)) A) ∥₀)
               → π-comp (1 + n) p q ≡ π-comp (1 + n) q p
Eckmann-Hilton-π {A = (A , pt)} n = elim2 (λ x y → isOfHLevelPath 2 setTruncIsSet _ _)
                                           λ p q → cong ∣_∣₀ (Eckmann-Hilton n p q)

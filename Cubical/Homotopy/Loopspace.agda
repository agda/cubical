{-# OPTIONS --cubical --no-import-sorts --safe #-}

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

Eckmann-Hilton : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) (α β : typ ((Ω^ (2 + n)) A))
              → α ∙ β ≡ β ∙ α
Eckmann-Hilton {A = A} n α β i =
  comp (λ k → rUnit (snd ((Ω^ (1 + n)) A)) (~ k) ≡ rUnit (snd ((Ω^ (1 + n)) A)) (~ k)) -- note : rUnit refl := lUnit refl
       (λ k → λ { (i = i0) → (cong (λ x → rUnit x (~ k)) α) ∙ cong (λ x → lUnit x (~ k)) β
               ;  (i = i1) → (cong (λ x → lUnit x (~ k)) β) ∙ cong (λ x → rUnit x (~ k)) α})
       ((λ j → α (j ∧ ~ i) ∙ β (j ∧ i)) ∙ λ j → α (~ i ∨ j) ∙ β (i ∨ j))

{- Homotopy group version -}
π-comp : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) → ∥ typ ((Ω^ (suc n)) A) ∥₂
      → ∥ typ ((Ω^ (suc n)) A) ∥₂ → ∥ typ ((Ω^ (suc n)) A) ∥₂
π-comp n = elim2 (λ _ _ → setTruncIsSet) λ p q → ∣ p ∙ q ∣₂

Eckmann-Hilton-π : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) (p q : ∥ typ ((Ω^ (2 + n)) A) ∥₂)
               → π-comp (1 + n) p q ≡ π-comp (1 + n) q p
Eckmann-Hilton-π  n = elim2 (λ x y → isOfHLevelPath 2 setTruncIsSet _ _)
                             λ p q → cong ∣_∣₂ (Eckmann-Hilton n p q)

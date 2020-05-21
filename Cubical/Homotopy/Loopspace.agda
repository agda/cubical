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


generalEH : {ℓ : Level} {A : Type ℓ} {a b c : A} {p q : a ≡ b} {r s : b ≡ c} (α : p ≡ q) (β : r ≡ s)
         → (cong (λ x → x ∙ r) α) ∙ (cong (λ x → q ∙ x) β)
          ≡ (cong (λ x → p ∙ x) β) ∙ (cong (λ x → x ∙ s) α)
generalEH {p = p} {r = r} α β j i =
   hcomp (λ k → λ { (i = i0) → p ∙ r
                   ; (i = i1) → α (k ∨ ~ j) ∙ β (k ∨ j) })
         (α (~ j ∧ i) ∙ β (j ∧ i))

Eckmann-Hilton : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) (α β : typ ((Ω^ (2 + n)) A))
              → α ∙ β ≡ β ∙ α
Eckmann-Hilton {A = A} n α β i =
  comp (λ k → rUnit (snd ((Ω^ (1 + n)) A)) (~ k) ≡ rUnit (snd ((Ω^ (1 + n)) A)) (~ k))
               -- note : rUnit refl := lUnit refl
       (λ k → λ { (i = i0) → (cong (λ x → rUnit x (~ k)) α) ∙ cong (λ x → lUnit x (~ k)) β
                ;  (i = i1) → (cong (λ x → lUnit x (~ k)) β) ∙ cong (λ x → rUnit x (~ k)) α})
       (generalEH α β i)

{- Homotopy group version -}
π-comp : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) → ∥ typ ((Ω^ (suc n)) A) ∥₀
      → ∥ typ ((Ω^ (suc n)) A) ∥₀ → ∥ typ ((Ω^ (suc n)) A) ∥₀
π-comp n = elim2 (λ _ _ → setTruncIsSet) λ p q → ∣ p ∙ q ∣₀

Eckmann-Hilton-π : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) (p q : ∥ typ ((Ω^ (2 + n)) A) ∥₀)
               → π-comp (1 + n) p q ≡ π-comp (1 + n) q p
Eckmann-Hilton-π  n = elim2 (λ x y → isOfHLevelPath 2 setTruncIsSet _ _)
                             λ p q → cong ∣_∣₀ (Eckmann-Hilton n p q)

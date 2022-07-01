{-# OPTIONS --safe #-}
module Cubical.Algebra.AbGroup.Properties where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.AbGroup.Base


private variable
  ℓ : Level

module AbGroupTheory (A : AbGroup ℓ) where

  open AbGroupStr (snd A)

  comm-4 : ∀ a b c d → (a + b) + (c + d) ≡ (a + c) + (b + d)
  comm-4 a b c d =
                 (a + b) + (c + d)  ≡⟨ +Assoc (a + b) c d ⟩
                 ((a + b) + c) + d  ≡⟨ cong (λ X → X + d) (sym (+Assoc a b c)) ⟩
                 (a + (b + c)) + d  ≡⟨ cong (λ X → (a + X) + d) (+Comm b c) ⟩
                 (a + (c + b)) + d  ≡⟨ cong (λ X → X + d) (+Assoc a c b) ⟩
                 ((a + c) + b) + d  ≡⟨ sym (+Assoc (a + c) b d) ⟩
                 (a + c) + (b + d)  ∎

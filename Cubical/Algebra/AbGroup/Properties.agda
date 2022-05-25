{-# OPTIONS --safe #-}
module Cubical.Algebra.AbGroup.Properties where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.AbGroup.Base


private variable
  ℓ : Level

module AbGroupTheory (A'@(A , Ar) : AbGroup ℓ) where

  open AbGroupStr Ar

  comm-4 : (a b c d : A) → ((a + b) + (c + d) ≡ (a + c) + (b + d))
  comm-4 a b c d = ((a + b) + (c + d)  ≡⟨ assoc (a + b) c d ⟩
                   (((a + b) + c) + d) ≡⟨ cong (λ X → X + d) (sym (assoc a b c)) ⟩
                   ((a + (b + c)) + d) ≡⟨ cong (λ X → (a + X) + d) (comm b c) ⟩
                   ((a + (c + b)) + d) ≡⟨ cong (λ X → X + d) (assoc a c b) ⟩
                   (((a + c) + b) + d) ≡⟨ sym (assoc (a + c) b d) ⟩
                   ((a + c) + (b + d)) ∎)

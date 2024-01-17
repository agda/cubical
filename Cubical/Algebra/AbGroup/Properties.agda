{-# OPTIONS --safe #-}
module Cubical.Algebra.AbGroup.Properties where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties

private variable
  ℓ : Level

module AbGroupTheory (A : AbGroup ℓ) where
  open GroupTheory (AbGroup→Group A)
  open AbGroupStr (snd A)

  comm-4 : ∀ a b c d → (a + b) + (c + d) ≡ (a + c) + (b + d)
  comm-4 a b c d =
                 (a + b) + (c + d)  ≡⟨ +Assoc (a + b) c d ⟩
                 ((a + b) + c) + d  ≡⟨ cong (λ X → X + d) (sym (+Assoc a b c)) ⟩
                 (a + (b + c)) + d  ≡⟨ cong (λ X → (a + X) + d) (+Comm b c) ⟩
                 (a + (c + b)) + d  ≡⟨ cong (λ X → X + d) (+Assoc a c b) ⟩
                 ((a + c) + b) + d  ≡⟨ sym (+Assoc (a + c) b d) ⟩
                 (a + c) + (b + d)  ∎

  implicitInverse : ∀ {a b} → a + b ≡ 0g → b ≡ - a
  implicitInverse b+a≡0 = invUniqueR b+a≡0

addGroupHom : (A B : AbGroup ℓ) (ϕ ψ : AbGroupHom A B) → AbGroupHom A B
fst (addGroupHom A B ϕ ψ) x = AbGroupStr._+_ (snd B) (ϕ .fst x) (ψ .fst x) 
snd (addGroupHom A B ϕ ψ) = makeIsGroupHom
  λ x y → cong₂ (AbGroupStr._+_ (snd B))
                 (IsGroupHom.pres· (snd ϕ) x y)
                 (IsGroupHom.pres· (snd ψ) x y)
        ∙ AbGroupTheory.comm-4 B (fst ϕ x) (fst ϕ y) (fst ψ x) (fst ψ y)

negGroupHom : (A B : AbGroup ℓ) (ϕ : AbGroupHom A B) → AbGroupHom A B
fst (negGroupHom A B ϕ) x = AbGroupStr.-_ (snd B) (ϕ .fst x)
snd (negGroupHom A B ϕ) =
  makeIsGroupHom λ x y
    → sym (IsGroupHom.presinv (snd ϕ) (AbGroupStr._+_ (snd A) x y))
     ∙ cong (fst ϕ) (GroupTheory.invDistr (AbGroup→Group A) x y
                  ∙ AbGroupStr.+Comm (snd A) _ _)
     ∙ IsGroupHom.pres· (snd ϕ) _ _
     ∙ cong₂ (AbGroupStr._+_ (snd B))
             (IsGroupHom.presinv (snd ϕ) x)
             (IsGroupHom.presinv (snd ϕ) y)

subtrGroupHom : (A B : AbGroup ℓ) (ϕ ψ : AbGroupHom A B) → AbGroupHom A B
subtrGroupHom A B ϕ ψ = addGroupHom A B ϕ (negGroupHom A B ψ)

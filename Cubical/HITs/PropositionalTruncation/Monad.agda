{-
Implements the monadic interface of propositional truncation, for reasoning in do-syntax.
-}

module Cubical.HITs.PropositionalTruncation.Monad where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Functions.Logic
open import Cubical.HITs.PropositionalTruncation

private
  variable
    ℓ : Level
    P Q : Type ℓ

infix 1 proof_by_
proof_by_ : (P : hProp ℓ) → ∥ ⟨ P ⟩ ∥₁ → ⟨ P ⟩
proof P by p = rec (isProp⟨⟩ P) (λ p → p) p

return : P → ∥ P ∥₁
return p = ∣ p ∣₁

exact_ : ∥ P ∥₁ → ∥ P ∥₁
exact p = p

_>>=_ : ∥ P ∥₁ → (P → ∥ Q ∥₁) → ∥ Q ∥₁
p >>= f = rec isPropPropTrunc f p

_>>_ : ∥ P ∥₁ → ∥ Q ∥₁ → ∥ Q ∥₁
_ >> q = q

{-

A parameterized family of structures S can be combined into a single structure:
X ↦ (a : A) → S a X

This is more general than Structures.Function in that S can vary in A.

-}
module Cubical.Structures.Parameterized where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Functions.FunExtEquiv
open import Cubical.Foundations.SIP
open import Cubical.Foundations.Univalence

private
  variable
    ℓ ℓ₁ ℓ₁' : Level

module _ {ℓ₀} (A : Type ℓ₀) where

  ParamStructure : (S : A → Type ℓ → Type ℓ₁)
    → Type ℓ → Type (ℓ-max ℓ₀ ℓ₁)
  ParamStructure S X = (a : A) → S a X

  ParamEquivStr : {S : A → Type ℓ → Type ℓ₁}
    → (∀ a → StrEquiv (S a) ℓ₁') → StrEquiv (ParamStructure S) (ℓ-max ℓ₀ ℓ₁')
  ParamEquivStr ι (X , l) (Y , m) e = ∀ a → ι a (X , l a) (Y , m a) e

  paramUnivalentStr : {S : A → Type ℓ → Type ℓ₁}
    (ι : ∀ a → StrEquiv (S a) ℓ₁') (θ : ∀ a → UnivalentStr (S a) (ι a))
    → UnivalentStr (ParamStructure S) (ParamEquivStr ι)
  paramUnivalentStr ι θ e = compEquiv (equivΠCod λ a → θ a e) funExtEquiv

  paramEquivAction : {S : A → Type ℓ → Type ℓ₁}
    → (∀ a → EquivAction (S a)) → EquivAction (ParamStructure S)
  paramEquivAction α e = equivΠCod (λ a → α a e)

  paramTransportStr : {S : A → Type ℓ → Type ℓ₁}
    (α : ∀ a → EquivAction (S a)) (τ : ∀ a → TransportStr (α a))
    → TransportStr (paramEquivAction α)
  paramTransportStr {S = S} α τ e f =
    funExt λ a →
    τ a e (f a)
    ∙ cong (λ fib → transport (λ i → S (fib .snd (~ i)) (ua e i)) (f (fib .snd i1)))
      (isContrSingl a .snd (_ , sym (transportRefl a)))

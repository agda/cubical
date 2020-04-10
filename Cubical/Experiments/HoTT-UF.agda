{-

This is a HoTT-UF core library based on cubical type theory, where the
cubical machinery is hidden, using the HoTT Book terminology and
notation.

The point is that function extensionality, propositional truncation
and univalence compute (an example is given below).

For the moment, this requires the development version of Agda.

-}

{-# OPTIONS --cubical --exact-split --safe #-}

module Cubical.Foundations.HoTT-UF where

open import Cubical.Core.Primitives hiding ( _≡_ )
open import Cubical.Core.Id public

open import Cubical.Foundations.Id public
     using ( _≡_            -- The identity type.
           ; refl           -- Unfortunately, pattern matching on refl is not available.
           ; J              -- Until it is, you have to use the induction principle J.

           ; transport      -- As in the HoTT Book.
           ; ap
           ; _∙_
           ; _⁻¹

           ; _≡⟨_⟩_         -- Standard equational reasoning.
           ; _∎

           ; funExt         -- Function extensionality
                            -- (can also be derived from univalence).

           ; Σ              -- Sum type. Needed to define contractible types, equivalences
           ; _,_            -- and univalence.
           ; pr₁            -- The eta rule is available.
           ; pr₂

           ; isProp         -- The usual notions of proposition, contractible type, set.
           ; isContr
           ; isSet

           ; isEquiv        -- A map with contractible fibers
                            -- (Voevodsky's version of the notion).
           ; _≃_            -- The type of equivalences between two given types.
           ; EquivContr     -- A formulation of univalence.

           ; ∥_∥             -- Propositional truncation.
           ; ∣_∣             -- Map into the propositional truncation.
           ; ∥∥-isProp       -- A truncated type is a proposition.
           ; ∥∥-recursion    -- Non-dependent elimination.
           ; ∥∥-induction    -- Dependent elimination.
           )

{-

Here is an illustration of how function extensionality computes.

-}

private

  data ℕ : Type₀ where
   zero : ℕ
   succ : ℕ → ℕ

  f g : ℕ → ℕ

  f n = n

  g zero = zero
  g (succ n) = succ (g n)

  h : (n : ℕ) → f n ≡ g n
  h zero = refl
  h (succ n) = ap succ (h n)

  p : f ≡ g
  p = funExt h

  five : ℕ
  five = succ (succ (succ (succ (succ zero))))

  a : Σ ℕ (λ n → f n ≡ five)
  a = five , refl

  b : Σ ℕ (λ n → g n ≡ five)
  b = transport (λ - → Σ ℕ (λ n → - n ≡ five)) p a

  c : pr₁ b ≡ five
  c = refl

{-

If we had funExt as a postulate, then the definition of c would not
type check. Moreover, the term pr₁ b would not evaluate to five, as it
does with the cubical type theory implementation of funext.

TODO. A similar computational example with univalence.

-}

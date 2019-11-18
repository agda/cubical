{-

This file contains:

- Definitions equivalences

- Glue types

-}
{-# OPTIONS --cubical --safe #-}
module Cubical.Core.Glue where

open import Cubical.Core.Primitives

open import Agda.Builtin.Cubical.Glue public
  using ( isEquiv       -- ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B) → Type (ℓ ⊔ ℓ')

        ; equiv-proof   -- ∀ (y : B) → isContr (fiber f y)

        ; _≃_           -- ∀ {ℓ ℓ'} (A : Type ℓ) (B : Type ℓ') → Type (ℓ ⊔ ℓ')

        ; equivFun      -- ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → A ≃ B → A → B

        ; equivProof    -- ∀ {ℓ ℓ'} (T : Type ℓ) (A : Type ℓ') (w : T ≃ A) (a : A) φ →
                        -- Partial φ (fiber (equivFun w) a) → fiber (equivFun w) a

        ; primGlue      -- ∀ {ℓ ℓ'} (A : Type ℓ) {φ : I} (T : Partial φ (Type ℓ'))
                        -- → (e : PartialP φ (λ o → T o ≃ A)) → Type ℓ'

        ; prim^unglue   -- ∀ {ℓ ℓ'} {A : Type ℓ} {φ : I} {T : Partial φ (Type ℓ')}
                        -- → {e : PartialP φ (λ o → T o ≃ A)} → primGlue A T e → A

        -- The ∀ operation on I. This is commented out as it is not currently used for anything
        -- ; primFaceForall -- (I → I) → I
        )
  renaming ( prim^glue   to glue         -- ∀ {ℓ ℓ'} {A : Type ℓ} {φ : I} {T : Partial φ (Type ℓ')}
                                         -- → {e : PartialP φ (λ o → T o ≃ A)}
                                         -- → PartialP φ T → A → primGlue A T e

           ; pathToEquiv to lineToEquiv  -- ∀ {ℓ : I → Level} (P : (i : I) → Type (ℓ i)) → P i0 ≃ P i1
           )

private
  variable
    ℓ ℓ' : Level

-- Uncurry Glue to make it more pleasant to use
Glue : (A : Type ℓ) {φ : I}
       → (Te : Partial φ (Σ[ T ∈ Type ℓ' ] T ≃ A))
       → Type ℓ'
Glue A Te = primGlue A (λ x → Te x .fst) (λ x → Te x .snd)

-- Make the φ argument of prim^unglue explicit
unglue : {A : Type ℓ} (φ : I) {T : Partial φ (Type ℓ')}
         {e : PartialP φ (λ o → T o ≃ A)} → primGlue A T e → A
unglue φ = prim^unglue {φ = φ}

-- People unfamiliar with [Glue], [glue] and [uglue] can find the types below more
-- informative as they demonstrate the computational behavior.
--
-- Full inference rules can be found in Section 6 of CCHM:
-- https://arxiv.org/pdf/1611.02108.pdf
-- Cubical Type Theory: a constructive interpretation of the univalence axiom
-- Cyril Cohen, Thierry Coquand, Simon Huber, Anders Mörtberg
private

  Glue-S : (A : Type ℓ) {φ : I}
         → (Te : Partial φ (Σ[ T ∈ Type ℓ' ] T ≃ A))
         → Sub (Type ℓ') φ (λ { (φ = i1) → Te 1=1 .fst })
  Glue-S A Te = inS (Glue A Te)

  glue-S :
   ∀ {A : Type ℓ} {φ : I}
   → {T : Partial φ (Type ℓ')} {e : PartialP φ (λ o → T o ≃ A)}
   → (t : PartialP φ T)
   → Sub A φ (λ { (φ = i1) → e 1=1 .fst (t 1=1) })
   → Sub (primGlue A T e) φ (λ { (φ = i1) → t 1=1 })
  glue-S t s = inS (glue t (outS s))

  unglue-S :
    ∀ {A : Type ℓ} (φ : I)
    {T : Partial φ (Type ℓ')} {e : PartialP φ (λ o → T o ≃ A)}
    → (x : primGlue A T e)
    → Sub A φ (λ { (φ = i1) → e 1=1 .fst x })
  unglue-S φ x = inS (prim^unglue {φ = φ} x)

{-

This file contains:

- Definitions equivalences

- Glue types

-}
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

  module GluePrims (A : Type ℓ) {φ : I} (Te : Partial φ (Σ[ T ∈ Type ℓ' ] T ≃ A)) where
    T : Partial φ (Type ℓ')
    T φ1 = Te φ1 .fst
    e : PartialP φ (λ φ → T φ ≃ A)
    e φ1 = Te φ1 .snd

    -- Glue can be seen as a subtype of Type that, at φ, is definitionally equal to the left type
    -- of the given equivalences.
    Glue-S : Type ℓ' [ φ ↦ T ]
    Glue-S = inS (Glue A Te)

    -- Which means partial elements of T are partial elements of Glue
    coeT→G :
      ∀ (t : PartialP φ T)
      → Partial φ (Glue A Te)
    coeT→G t (φ = i1) = t 1=1

    -- ... and elements of Glue can be seen as partial elements of T
    coeG→T :
      ∀ (g : Glue A Te)
      → PartialP φ T
    coeG→T g (φ = i1) = g

    -- What about elements that are applied to the equivalences?
    trans-e :
      ∀ (t : PartialP φ T)
      → Partial φ A
    trans-e t ϕ1 = equivFun (e ϕ1) (t ϕ1)

    -- glue gives a partial element of Glue given an element of A. Note that it "undoes"
    -- the application of the equivalences!
    glue-S :
      ∀ (t : PartialP φ T)
      → A [ φ ↦ trans-e t ]
      → Glue A Te [ φ ↦ coeT→G t ]
    glue-S t s = inS (glue t (outS s))

    -- typechecking glue enforces this, e.g. you can not simply write
    -- glue-bad : (t : PartialP φ T) → A → Glue A Te
    -- glue-bad t s = glue t s

    -- unglue does the inverse:
    unglue-S :
      ∀ (b : Glue A Te)
      → A [ φ ↦ trans-e (coeG→T b) ]
    unglue-S b = inS (unglue φ b)

  module GlueTransp (A : I → Type ℓ) (Te : (i : I) → Partial (i ∨ ~ i) (Σ[ T ∈ Type ℓ' ] T ≃ A i)) where
    A0 A1 : Type ℓ
    A0 = A i0
    A1 = A i1
    T : (i : I) → Partial (i ∨ ~ i) (Type ℓ')
    T i φ = Te i φ .fst
    e : (i : I) → PartialP (i ∨ ~ i) (λ φ → T i φ ≃ A i)
    e i φ = Te i φ .snd
    T0 T1 : Type ℓ'
    T0 = T i0 1=1
    T1 = T i1 1=1
    e0 : T0 ≃ A0
    e0 = e i0 1=1
    e1 : T1 ≃ A1
    e1 = e i1 1=1

    transportA : A0 → A1
    transportA = transp (λ i → A i) i0

    -- copied over from Foundations/Equiv for readability, can't directly import due to cyclic dependency
    invEq : ∀ {X : Type ℓ'} {ℓ''} {Y : Type ℓ''} (w : X ≃ Y) → Y → X
    invEq w y = w .snd .equiv-proof y .fst .fst

    -- transport in Glue reduces to transport in A + the application of the equivalences in forward and backward
    -- direction.
    transp-S : (t0 : T0) → T1 [ i1 ↦ (λ _ → invEq e1 (transportA (equivFun e0 t0))) ]
    transp-S t0 = inS (transp (λ i → Glue (A i) (Te i)) i0 t0)

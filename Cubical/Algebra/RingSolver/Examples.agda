{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.RingSolver.Examples where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.RingSolver.AlmostRing
open import Cubical.Algebra.RingSolver.NatAsAlmostRing
open import Cubical.Algebra.RingSolver.RingExpression
open import Cubical.Algebra.RingSolver.RawRing renaming (⟨_⟩ to ⟨_⟩ᵣ)

open import Cubical.Data.FinData
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Vec.Base

module _ where
  open AlmostRing ℕAsAlmostRing
  open Normalize ℕAsAlmostRing
  open Horner (AlmostRing→RawRing ℕAsAlmostRing)
  open Eval (AlmostRing→RawRing ℕAsAlmostRing)
  
  ExprX : Expr ℕ 1
  ExprX = ∣ (fromℕ 0)

  {- 
     Reify maps an expression to its Horner Normalform.
     Two expressions evaluating to the same ring element
     have the same Horner Normal form.
     This means equality of the represented ring elements
     can be checked by agda's unification (so refl is a proof)
   -}
  _ : Reify ((K 2) ⊗ ExprX) ≡
      Reify (ExprX ⊕ ExprX)
  _ = refl

  _ : Reify (ExprX ⊕ (K (1 + 1))) ≡
      Reify ((K 0) ⊗ ExprX ⊕ (K 1) ⊗ (K 2) ⊕ ExprX)
  _ = refl


  {-
    The solver needs to produce an equality between
    actual ring elements. So we need a proof that 
    those actual ring elements are equal to a normal form:
  -}
  _ : (x : ℕ) → evalH (Reify ((K 2) ⊗ ExprX)) x ≡ 2 · x
  _ = sound ((K 2) ⊗ ExprX)

  {-
    Now two of these proofs can be plugged together
    to solve an equation:
  -}
  _ : (x : ℕ) → 3 + x + x ≡ 1 + 2 · x + 1 + 1 
  _ = let
        lhs = (K 3) ⊕ ExprX ⊕ ExprX
        rhs = (K 1) ⊕ (K 2) ⊗ ExprX ⊕ (K 1) ⊕ (K 1) 
      in (λ x →   ⟦ lhs ⟧ (x ∷ [])    ≡⟨ sym (sound lhs x) ⟩
                  evalH (Reify lhs) x ≡⟨ refl ⟩
                  evalH (Reify rhs) x ≡⟨ sound rhs x ⟩
                  ⟦ rhs ⟧ (x ∷ [])    ∎)

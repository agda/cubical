{-

The Inductive Version of James Construction

This file contains:
  - An inductive family 𝕁, and its direct colimit is equivalence to James;
    (KANG Rongji, Feb. 2022)
  - The family 𝕁 can be iteratively constructed as pushouts;
  - Special cases of 𝕁 n for n = 0, 1 and 2;
  - Connectivity of inclusion maps.

This file is the summary of the main results.
The proof is divided into parts and put inside the fold Cubical.HITs.James.Inductive

-}
module Cubical.HITs.James.Inductive where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Pointed

open import Cubical.Data.Nat
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Sequence

open import Cubical.HITs.Wedge
open import Cubical.HITs.Pushout
open import Cubical.HITs.Pushout.PushoutProduct
open import Cubical.HITs.SequentialColimit

open import Cubical.HITs.James.Base
open import Cubical.HITs.James.Inductive.Base
open import Cubical.HITs.James.Inductive.PushoutFormula
  renaming (isConnectedIncl to connIncl ; isConnectedInl to connInl)
open import Cubical.HITs.James.Inductive.Reduced
open import Cubical.HITs.James.Inductive.ColimitEquivalence

open import Cubical.Homotopy.Connected

private
  variable
    ℓ : Level

module JamesInd
  (X∙@(X , x₀) : Pointed ℓ) where

  -- The family 𝕁 n is equivalence to Brunerie's J n, as will be shown latter.
  -- Instead of his inductive procedure, 𝕁 is defined directly as an indexed HIT.

  𝕁 : ℕ → Type ℓ
  𝕁 = 𝕁ames (X , x₀)

  -- This family forms a direct system.

  𝕁Seq : Sequence ℓ
  𝕁Seq = 𝕁amesSeq (X , x₀)

  -- The inductive construction of James is called 𝕁∞.
  -- It is the direct colimit of 𝕁 n.

  𝕁∞ : Type ℓ
  𝕁∞ = SeqColim 𝕁Seq

  -- And of course it is equivalent to James.

  J≃𝕁∞ : James (X , x₀) ≃ 𝕁∞
  J≃𝕁∞ = compEquiv (James≃𝕁Red∞ _) (invEquiv (𝕁ames∞≃𝕁Red∞ _))

  -- Special cases of 𝕁 n for n = 0, 1 and 2:

  𝕁₀≃Unit : 𝕁 0 ≃ Unit
  𝕁₀≃Unit = 𝕁ames0≃ _

  𝕁₁≃X : 𝕁 1 ≃ X
  𝕁₁≃X = 𝕁ames1≃ _

  𝕁₂≃P[X×X←X⋁X→X] : 𝕁 2 ≃ Pushout ⋁↪ fold⋁
  𝕁₂≃P[X×X←X⋁X→X] = 𝕁ames2≃ _

  -- The following is defined as pushouts of 𝕁 n.

  𝕁Push : ℕ → Type ℓ
  𝕁Push = 𝕁amesPush (X , x₀)

  -- Brunerie uses f and g to denote the following maps, so do I.

  module _
    {n : ℕ} where

    f : 𝕁Push n → X × 𝕁 (1 + n)
    f = leftMap _

    g : 𝕁Push n → 𝕁 (1 + n)
    g = rightMap _

  -- Here we show that 𝕁 (n+2) can be made as double pushouts invoving only X, 𝕁 n and 𝕁 (n+1).
  -- In particular, our 𝕁 is exactly what Brunerie had defined.

  𝕁ₙ₊₂≃Pushout : (n : ℕ) → 𝕁 (2 + n) ≃ Pushout f g
  𝕁ₙ₊₂≃Pushout = 𝕁ames2+n≃ _

  -- Connectivity of inclusion maps:

  module _
    (d : ℕ)(conn : isConnected (1 + d) X) where

    -- Warning:
    -- The connectivity is shifted by 2 from the convention of usual homotopy theory.

    -- If X is (d+1)-connected, the transition incl : 𝕁 n → 𝕁 (n+1) will be (n+1)d-connected.

    isConnectedIncl : (n : ℕ) → isConnectedFun ((1 + n) · d) (incl {n = n})
    isConnectedIncl = connIncl X∙ d conn

    -- If X is (d+1)-connected, the inclusion inl : 𝕁 n → 𝕁∞ will be (n+1)d-connected.

    inl∞ : (n : ℕ) → 𝕁 n → 𝕁∞
    inl∞ _ = incl

    isConnectedInl : (n : ℕ) → isConnectedFun ((1 + n) · d) (inl∞ n)
    isConnectedInl = connInl X∙ d conn

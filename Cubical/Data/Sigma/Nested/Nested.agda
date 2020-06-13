{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Data.Sigma.Nested.Nested where

open import Cubical.Core.Everything

open import Cubical.Data.Nat
open import Cubical.Data.Sigma


open import Cubical.Foundations.Everything

open import Cubical.Data.Sigma.Nested.Base


-- crude (temporary) name "Par" for this datatype
-- comes from Parenthesis
--
-- it is clearly binary tree, but without any data atached to nodes, or leafs
--
-- maybe this should be datatype on its own ?
-- what would be the good name for it?
--
-- I have version of this where Par is indexed by its "length",
-- but this verision was shorter
--
-- this datatype is used to describe different ways to apply multiple Σ
-- to create NestedΣ type
--

data Par : Type₀ where
  □ : Par
  [-_-_-] : Par → Par → Par

leftMost : ℕ → Par
leftMost zero = □
leftMost (suc n) = [- leftMost n - □ -]

rigthMost : ℕ → Par
rigthMost zero = □
rigthMost (suc n) = [- □ - rigthMost n -]


len : Par → ℕ
len □ = 1
len [- x - x₁ -] = len x + len x₁



NestedΣ : ∀ {ℓ} → ∀ sh → Sig ℓ (len sh) → Type ℓ


-- for any signature, there is isomorphism betwen NestedΣᵣ (nested Sigma in rigtmost shape)
-- and NestedΣ sh (nested Sigma in shape described by the argument of type Par)

NestedΣ-NestedΣᵣ-Iso : ∀ {ℓ} → (sh : Par) → (s : Sig ℓ (len sh))
                      → Iso (NestedΣ sh s) (NestedΣᵣ s) 

NestedΣ □ x = x
NestedΣ [- shL - shR -] s =
   let (sL , sR) = sig-cs.split {n = len shL} {m = len shR} s
   in Σ (NestedΣ shL sL) (NestedΣ shR ∘ sR ∘ Iso.fun (NestedΣ-NestedΣᵣ-Iso shL _))

NestedΣ-NestedΣᵣ-Iso □ s = idIso
NestedΣ-NestedΣᵣ-Iso [- shL - shR -] s = 
  let (sL , sR) = sig-cs.split {n = len shL} {m = len shR} s 
  in compIso (Σ-cong-iso-snd λ _ → NestedΣ-NestedΣᵣ-Iso shR _)
      (compIso (Σ-cong-iso-fst {B = NestedΣᵣ ∘ sR} (NestedΣ-NestedΣᵣ-Iso shL sL))
        (nestedΣᵣ-cs.isom {n = len shL} {m = len shR} s))


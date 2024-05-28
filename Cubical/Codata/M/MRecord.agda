{- Alternative definition of M as a record type, together with some of its properties

-}

{-# OPTIONS --cubical --safe #-}

open import Cubical.Foundations.Prelude

module Cubical.Codata.M.MRecord where

record M' (S : Type) (P : S → Type) : Type where
  constructor sup-M
  coinductive
  field
    shape : S
    pos : P shape → M' S P
open M'

-- Lifting M' to relations
record M'-R {S : Type} {Q : S → Type} (R : M' S Q → M' S Q → Type) (m₀ m₁ : M' S Q) : Type where
  field
   s-eq : shape m₀ ≡ shape m₁        
   p-eq : (q₀ : Q (shape m₀))(q₁ : Q (shape m₁))(q-eq : PathP (λ i → Q (s-eq i)) q₀ q₁)
          → R (pos m₀ q₀) (pos m₁ q₁)
open M'-R

-- (Propositional) η-equality for M'
ηEqM' : {S' : Type} {Q' : S' → Type} (m : M' S' Q') → sup-M (shape m) (pos m) ≡ m
shape (ηEqM' m i) = shape m
pos (ηEqM' m i) = pos m

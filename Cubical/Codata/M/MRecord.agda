{- Alternative definition of M as a record type, together with some of its properties

-}

{-# OPTIONS --cubical --guardedness --safe #-}

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

-- Coinduction principle for M
CoInd-M' : {S : Type} {Q : S → Type} (R : M' S Q → M' S Q → Type)
          (is-bisim : {m₀ m₁ : M' S Q} → R m₀ m₁ → M'-R R m₀ m₁)
          {m₀ m₁ : M' S Q} → R m₀ m₁ → m₀ ≡ m₁ 
shape (CoInd-M' R is-bisim r i) = s-eq (is-bisim r) i
pos (CoInd-M' {S} {Q} R is-bisim {m₀ = m₀}{m₁ = m₁} r i) q =
  CoInd-M' R is-bisim {m₀ = pos m₀ q₀} {m₁ = pos m₁ q₁} (p-eq (is-bisim r) q₀ q₁ q₂) i
    where QQ : I → Type
          QQ i = Q (s-eq (is-bisim r) i)

          q₀ : QQ i0
          q₀ = transp (λ j → QQ (~ j ∧ i)) (~ i) q

          q₁ : QQ i1
          q₁ = transp (λ j → QQ (j ∨ i)) i q

          q₂ : PathP (λ i → QQ i) q₀ q₁
          q₂ k = transp (λ j → QQ ((~ k ∧ ~ j ∧ i) ∨ (k ∧ (j ∨ i)) ∨
                 ((~ j ∧ i) ∧ (j ∨ i)))) ((~ k ∧ ~ i) ∨ (k ∧ i)) q
                 
-- (Propositional) η-equality for M'
M'-eta-eq : {S' : Type} {Q' : S' → Type} (m : M' S' Q') → sup-M (shape m) (pos m) ≡ m
shape (M'-eta-eq m i) = shape m
pos (M'-eta-eq m i) = pos m

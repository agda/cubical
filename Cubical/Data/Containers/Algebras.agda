{- Basic definitions required for co/inductive container proofs

- Proposition elimination

- Definition of Pos

-}

{-# OPTIONS --cubical --guardedness --safe #-}

open import Cubical.Data.W
open import Cubical.Codata.M.MRecord renaming (M' to M)
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude

module Cubical.Data.Containers.Algebras where

-- Proposition elimination
prop-elim : ∀ {ℓ} {A : Type ℓ} (t : isProp A) → (D : A → Type ℓ) →
            (x : A) → D x → (a : A) → D a
prop-elim t D x pr a = subst D (t x a) pr

module Algs (Ind : Type)
         (S : Type)
         (P : Ind → S → Type)
         (Q : S → Type)
         (X : Ind → Type)
         (Y : Type) where

  open M
  open Iso

  -- Fixed point algebras
  record ContFuncIso (S : Type) (P : S → Type) : Type₁ where
    constructor iso
    field
      carrier : Type
      χ : Iso (Σ[ s ∈ S ] (P s → carrier)) carrier

  open ContFuncIso

  WAlg : ContFuncIso S Q
  WAlg = iso (W S Q) isom
    where
      isom : Iso (Σ[ s ∈ S ] (Q s → W S Q)) (W S Q)
      fun isom = uncurry sup-W
      inv isom (sup-W s f) = s , f
      rightInv isom (sup-W s f) = refl
      leftInv isom (s , f) = refl

  MAlg : ContFuncIso S Q
  MAlg = iso (M S Q) isom
    where
      isom : Iso (Σ[ s ∈ S ] (Q s → M S Q)) (M S Q)
      fun isom = uncurry sup-M
      inv isom m = shape m , pos m
      rightInv isom m = M'-eta-eq m
      leftInv isom (s , f) = refl

  data Pos (FP : ContFuncIso S Q) (i : Ind) : carrier FP → Type where
    here : {wm : carrier FP} → P i (fst (FP .χ .inv wm)) → Pos FP i wm
    below : {wm : carrier FP} → (q : Q (fst (FP .χ .inv wm))) →
            Pos FP i (snd (FP .χ .inv wm) q) → Pos FP i wm


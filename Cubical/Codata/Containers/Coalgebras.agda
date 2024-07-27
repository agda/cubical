{-# OPTIONS --safe --guardedness #-}

module Cubical.Codata.Containers.Coalgebras where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function

open import Cubical.Codata.M.MRecord
open import Cubical.Data.Containers.Algebras

private
  variable
    ℓ ℓ' : Level

module Coalgs (S : Type ℓ) (Q : S → Type ℓ') where
  open Algs S Q
  open Iso
  open M

  MAlg : FixedPoint
  MAlg = iso (M S Q) isom
    where
      isom : Iso (Σ[ s ∈ S ] (Q s → M S Q)) (M S Q)
      fun isom = uncurry sup-M
      inv isom m = shape m , pos m
      rightInv isom m = ηEqM m
      leftInv isom (s , f) = refl

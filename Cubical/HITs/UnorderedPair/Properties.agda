{-# OPTIONS --safe #-}
module Cubical.HITs.UnorderedPair.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.HITs.SetCoequalizer as SQ

open import Cubical.HITs.UnorderedPair.Base as UP

open Iso

private variable
  ℓ : Level
  A : Type ℓ

SetCoequalizerPair : Type ℓ → Type ℓ
SetCoequalizerPair A = SetCoequalizer (idfun (A × A)) (λ (a , b) → b , a)

SetCoeq→UPair : SetCoequalizerPair A → UnorderedPair A
SetCoeq→UPair = SQ.rec trunc (uncurry _,_) (uncurry swap)

UPair→SetCoeq : UnorderedPair A → SetCoequalizerPair A
UPair→SetCoeq = UP.rec squash (curry inc) (curry coeq)

SetCoeq→UPair→SetCoeq : (xs : UnorderedPair A) → SetCoeq→UPair (UPair→SetCoeq xs) ≡ xs
SetCoeq→UPair→SetCoeq = UP.elimProp (trunc _ _) λ _ _ → refl

UPair→SetCoeq→SetCoeq : (xs : SetCoequalizerPair A) → UPair→SetCoeq (SetCoeq→UPair xs) ≡ xs
UPair→SetCoeq→SetCoeq = SQ.elimProp (λ _ → squash _ _) λ _ → refl

SetCoeqIsoUPair : Iso (SetCoequalizerPair A) (UnorderedPair A)
fun SetCoeqIsoUPair = SetCoeq→UPair
inv SetCoeqIsoUPair = UPair→SetCoeq
rightInv SetCoeqIsoUPair = SetCoeq→UPair→SetCoeq
leftInv SetCoeqIsoUPair = UPair→SetCoeq→SetCoeq

SetCoeq≡UPair : SetCoequalizerPair A ≡ UnorderedPair A
SetCoeq≡UPair = isoToPath SetCoeqIsoUPair

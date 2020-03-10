{-# OPTIONS --cubical --guardedness #-} --safe

open import Cubical.M-types.M-type

open import Cubical.Data.Unit
open import Cubical.Data.Sum
open import Cubical.Data.Prod
open import Cubical.Data.Nat
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.Data.List
open import Cubical.Foundations.Univalence

module Cubical.M-types.stream where

--------------------------------------
-- Stream definitions using M-types --
--------------------------------------

stream-S : ∀ A -> Container
stream-S A = (A , (λ _ → Unit))

stream : ∀ (A : Set₀) -> Set₀
stream A = M-type (stream-S A)

cons : ∀ {A} -> A -> stream A -> stream A
cons x xs = in-fun (x , λ { tt -> xs } )

hd : ∀ {A} -> stream A -> A
hd {A} S = out-fun S .fst

tl : ∀ {A} -> stream A -> stream A
tl {A} S = out-fun S .snd tt

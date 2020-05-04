{-# OPTIONS --cubical --guardedness --safe #-}

module Cubical.Codata.M-types.stream where

open import Cubical.Data.Unit

open import Cubical.Foundations.Prelude

open import Cubical.Codata.M-types.M-type
open import Cubical.Codata.M-types.helper
open import Cubical.Codata.M-types.Container

--------------------------------------
-- Stream definitions using M-types --
--------------------------------------

stream-S : ∀ A -> Container ℓ-zero
stream-S A = (A , (λ _ → Unit))

stream : ∀ (A : Type₀) -> Type₀
stream A = M-type (stream-S A)

cons : ∀ {A} -> A -> stream A -> stream A
cons x xs = in-fun (x , λ { tt -> xs } )

hd : ∀ {A} -> stream A -> A
hd {A} S = out-fun S .fst

tl : ∀ {A} -> stream A -> stream A
tl {A} S = out-fun S .snd tt

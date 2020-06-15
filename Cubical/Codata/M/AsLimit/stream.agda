{-# OPTIONS --cubical --no-import-sorts --guardedness --safe #-}

module Cubical.Codata.M.AsLimit.stream where

open import Cubical.Data.Unit

open import Cubical.Foundations.Prelude

open import Cubical.Codata.M.AsLimit.M
open import Cubical.Codata.M.AsLimit.helper
open import Cubical.Codata.M.AsLimit.Container

--------------------------------------
-- Stream definitions using M.AsLimit --
--------------------------------------

stream-S : ∀ A -> Container ℓ-zero
stream-S A = (A , (λ _ → Unit))

stream : ∀ (A : Type₀) -> Type₀
stream A = M (stream-S A)

cons : ∀ {A} -> A -> stream A -> stream A
cons x xs = in-fun (x , λ { tt -> xs } )

hd : ∀ {A} -> stream A -> A
hd {A} S = out-fun S .fst

tl : ∀ {A} -> stream A -> stream A
tl {A} S = out-fun S .snd tt

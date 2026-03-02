module Cubical.Data.IterativeSets.Empty where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

open import Cubical.Data.Empty renaming (elim* to ⊥*-elim ; elim to ⊥-elim)
open import Cubical.Functions.Embedding
open import Cubical.Relation.Nullary using (¬_)

open import Cubical.Data.IterativeMultisets.Base
open import Cubical.Data.IterativeSets.Base

private
  variable
    ℓ : Level
    x : V⁰ {ℓ}

empty⁰ : V⁰ {ℓ}
empty⁰ {ℓ} = fromEmb E
    where
        E : Embedding (V⁰ {ℓ}) ℓ
        E .fst = ⊥*
        E .snd .fst ()
        E .snd .snd ()

empty⁰' : V⁰ {ℓ}
empty⁰' .fst = emptySet-∞
empty⁰' .snd .fst ()
empty⁰' .snd .snd ()

El⁰empty⁰Is⊥* : El⁰ {ℓ} empty⁰ ≡ ⊥* {ℓ}
El⁰empty⁰Is⊥* = refl

empty⁰-is-empty : ¬ x ∈⁰ empty⁰
empty⁰-is-empty (⊥-inh , _) = ⊥*-elim ⊥-inh

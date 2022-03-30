{-# OPTIONS --safe #-}
module Cubical.Modalities.Flat.Cohomology where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Pointed

open import Cubical.Homotopy.Loopspace

open import Cubical.Data.Nat
open import Cubical.HITs.PropositionalTruncation as PropTrunc
open import Cubical.HITs.SetTruncation

open import Cubical.Modalities.Flat

module _ {@♭ ℓ : Level} (@♭ A : Pointed ℓ)
         (@♭ BA : Pointed ℓ) (isDelooping : Ω BA ≃∙ A)
         (@♭ conn : (x : fst BA) → ∥ x ≡ (snd BA) ∥ )
         where
  ♭∙ : (@♭ X : Pointed ℓ) → Pointed ℓ
  ♭∙ X = (♭ (fst X)) , ((snd X) ^♭)

  _ : Ω (♭∙ BA) ≃∙ ♭∙ (Ω BA)
  _ = ♭≡Comm _ _ , {!!}

  ♭IsDelooping : Ω (♭∙ BA) ≃∙ (♭∙ A)
  ♭IsDelooping = {!!}

  {-
    The following shouldn't be provable, if ♭ is a general Δ∘Γ.
    But it should be provable with crisp interval variables...
    On the other hand, I'm not really sure about the first claim anyway...
  -}
  ♭Conn : (x : fst (♭∙ BA)) → ∥ x ≡ (snd (♭∙ BA)) ∥
  ♭Conn (x ^♭) = PropTrunc.rec isPropPropTrunc (λ p → ∣ fst (invEquiv (♭≡Comm x (snd BA))) {! p ^♭!} ∣) (conn x)

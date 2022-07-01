{-# OPTIONS #-}
module Cubical.Modalities.Flat.CrispIdInduction where

open import Cubical.Foundations.Prelude

open import Cubical.Modalities.Flat.Base

{-
  From Theorem 5.6 in Michael Shulman's real cohesion article.
  It is unclear, if this is provable for path types, but it should work
  semantically and should be ok to assume as an axiom to reproduce
  real-cohesion.
-}
postulate
  crispIdentityInduction : {@♭ ♭ℓ ♭ℓ′ : Level} {@♭ B : Type ♭ℓ}
    (@♭ C : (@♭ u v : B) (@♭ p : u ≡ v) → Type ♭ℓ′)
    → (@♭ d : (@♭ u : B) → C u u refl)
    → (@♭ u v : B) (@♭ p : u ≡ v)
    → C u v p

{-
  This type ℕ₋₂ was originally used as the index to n-truncation in order to
   be consistent with the notation in the HoTT book. However, ℕ was already
   being used as an analogous index in Foundations.HLevels, and it became
   clear that having two different indexing schemes for truncation levels was
   very inconvenient. In the end, having slightly nicer notation was not worth
   the hassle of having to use this type everywhere where truncation levels
   were needed. So for this library, use the type `HLevel = ℕ` instead.

  See the discussions below for more context:
   - https://github.com/agda/cubical/issues/266
   - https://github.com/agda/cubical/pull/238
-}
module Cubical.Experiments.NatMinusTwo where

open import Cubical.Experiments.NatMinusTwo.Base public

open import Cubical.Experiments.NatMinusTwo.Properties public

open import Cubical.Experiments.NatMinusTwo.ToNatMinusOne using (1+_; ℕ₋₁→ℕ₋₂; -1+Path) public

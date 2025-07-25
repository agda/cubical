module Cubical.HITs.Localization.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv.PathSplit
open isPathSplitEquiv

open import Cubical.HITs.Localization.Base

module _ {ℓα ℓs ℓt} {A : Type ℓα} {S : A → Type ℓs} {T : A → Type ℓt} where

  rec : ∀ {F : ∀ α → S α → T α} {ℓ ℓ'} {X : Type ℓ} {Y : Type ℓ'}
        → (lY : isLocal F Y) → (X → Y) → Localize F X → Y
  rec lY g ∣ x ∣ = g x
  rec lY g (ext   α f t)   = fst (sec (lY α)) (λ s → rec lY g (f s)) t
  rec lY g (isExt α f s i) = snd (sec (lY α)) (λ s → rec lY g (f s)) i s
  rec lY f (≡ext   α g h p t i)   = fst (secCong (lY α) (λ t → rec lY f (g t)) (λ t → rec lY f (h t)))
                                        (λ i s → rec lY f (p s i)) i t
  rec lY f (≡isExt α g h p t i j) = snd (secCong (lY α) (λ t → rec lY f (g t)) (λ t → rec lY f (h t)))
                                        (λ i s → rec lY f (p s i)) i j t

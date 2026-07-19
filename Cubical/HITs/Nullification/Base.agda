module Cubical.HITs.Nullification.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv.PathSplit
open isPathSplitEquiv

module _ {ℓα ℓs} {A : Type ℓα} (S : A → Type ℓs) where
  isNull : ∀ {ℓ} (X : Type ℓ) → Type (ℓ-max (ℓ-max ℓα ℓs) ℓ)
  isNull X = (α : A) → isPathSplitEquiv (const {A = X} {B = S α})

  data Null {ℓ} (X : Type ℓ) : Type (ℓ-max (ℓ-max ℓα ℓs) ℓ) where
    ∣_∣ : X → Null X
    -- the image of every map (S α → Null S X) is contractible in Null S X
    hub   : (α : A) → (f : (S α) → Null X) → Null X
    spoke : (α : A) → (f : (S α) → Null X) (s : S α) → hub α f ≡ f s
    -- the image of every map (S α → x ≡ y) for x y : X is contractible in x ≡ y
    ≡hub   : ∀ {x y} {α} (p : S α → x ≡ y) → x ≡ y
    ≡spoke : ∀ {x y} {α} (p : S α → x ≡ y) (s : S α) → ≡hub p ≡ p s

  isNull-Null : ∀ {ℓ} {X : Type ℓ} → isNull (Null X)
  fst (sec (isNull-Null α)) f =     hub   α f
  snd (sec (isNull-Null α)) f i s = spoke α f s i
  fst (secCong (isNull-Null α) x y) p i     = ≡hub   (funExt⁻ p) i
  snd (secCong (isNull-Null α) x y) p i j s = ≡spoke (funExt⁻ p) s i j

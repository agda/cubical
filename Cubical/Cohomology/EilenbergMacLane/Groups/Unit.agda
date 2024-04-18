{-# OPTIONS --safe #-}

module Cubical.Cohomology.EilenbergMacLane.Groups.Unit where

open import Cubical.Cohomology.EilenbergMacLane.Base
open import Cubical.Cohomology.EilenbergMacLane.Groups.Connected

open import Cubical.Homotopy.EilenbergMacLane.Base
open import Cubical.Homotopy.EilenbergMacLane.Properties
open import Cubical.Homotopy.Connected

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Nat

open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.AbGroup.Base

open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.Truncation as Trunc

open import Cubical.Data.Unit

H⁰[Unit,G]≅G : ∀ {ℓ} {G : AbGroup ℓ}
  → AbGroupEquiv (coHomGr 0 G Unit) G
H⁰[Unit,G]≅G {G = G} = H⁰conn isConnectedUnit G
  where
  isConnectedUnit : isConnected 2 Unit
  fst isConnectedUnit = ∣ tt ∣
  snd isConnectedUnit = Trunc.elim (λ _ → isOfHLevelPath 2 (isOfHLevelTrunc 2) _ _)
                        λ _ → refl

isContr-Hⁿ⁺¹[Unit,G] : ∀ {ℓ} {G : AbGroup ℓ} (n : ℕ)
  → isContr (coHom (suc n) G Unit)
fst (isContr-Hⁿ⁺¹[Unit,G] {G = G} n) = 0ₕ (suc n)
snd (isContr-Hⁿ⁺¹[Unit,G] {G = G} n) =
  ST.elim (λ _ → isSetPathImplicit)
    λ f → Trunc.rec
      (isProp→isOfHLevelSuc n (squash₂ _ _))
      (λ p → cong ∣_∣₂ (funExt λ _ → p))
      (isConnectedPath (suc n)
        (isConnectedEM (suc n)) (0ₖ (suc n)) (f tt) .fst)

Hⁿ⁺¹[Unit,G]≅0 : ∀ {ℓ} {G : AbGroup ℓ} (n : ℕ)
  → AbGroupEquiv (coHomGr (suc n) G Unit) (trivialAbGroup {ℓ = ℓ})
fst (Hⁿ⁺¹[Unit,G]≅0 {G = G} n) = isoToEquiv (isContr→Iso (isContr-Hⁿ⁺¹[Unit,G] n) isContrUnit*)
snd (Hⁿ⁺¹[Unit,G]≅0 n) = makeIsGroupHom λ _ _ → refl

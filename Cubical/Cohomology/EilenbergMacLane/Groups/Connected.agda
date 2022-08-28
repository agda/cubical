{-# OPTIONS --safe #-}

module Cubical.Cohomology.EilenbergMacLane.Groups.Connected where

open import Cubical.Cohomology.EilenbergMacLane.Base

open import Cubical.Homotopy.Connected

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Nat

open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.AbGroup.Base

open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.Truncation as Trunc

private
  variable
    ℓ ℓ' : Level

module _ {A : Type ℓ} (conA : isConnected 2 A) (G : AbGroup ℓ') where
  private
    H⁰A = coHom 0 G A

    open AbGroupStr (snd G) renaming (_+_ to _+G_ ; -_ to -G_)

    a* : hLevelTrunc 2 A
    a* = conA .fst

  H⁰→G' : hLevelTrunc 2 A → H⁰A → fst G
  H⁰→G' = Trunc.rec (isSetΠ (λ _ → is-set))
            (λ a → ST.rec is-set λ f → f a)

  H⁰→G'-id : (a : hLevelTrunc 2 A) → H⁰→G' a* ≡ H⁰→G' a
  H⁰→G'-id a = cong H⁰→G' (conA .snd a)

  H⁰→G : H⁰A → fst G
  H⁰→G = H⁰→G' a*

  G→H⁰ : fst G → H⁰A
  G→H⁰ x = ∣ (λ _ → x) ∣₂

  G→H⁰→G : (x : fst G) → H⁰→G (G→H⁰ x) ≡ x
  G→H⁰→G = Trunc.rec (isSetΠ (λ _ → isOfHLevelPath 2 is-set _ _))
                       (λ a g i → H⁰→G'-id ∣ a ∣ i (G→H⁰ g)) a*

  H⁰→G→H⁰ : (x : H⁰A) → G→H⁰ (H⁰→G x) ≡ x
  H⁰→G→H⁰ = ST.elim (λ _ → isSetPathImplicit) λ f →
               Trunc.rec isSetPathImplicit
                 (λ a → (λ i → G→H⁰ (H⁰→G'-id ∣ a ∣ₕ i ∣ f ∣₂))
                       ∙ cong ∣_∣₂ (funExt λ x
                         → Trunc.rec (is-set _ _)
                           (cong f)
                           (Iso.fun (PathIdTruncIso 1)
                             (isContr→isProp conA ∣ a ∣ ∣ x ∣))))
                 a*

  private
    H⁰conn' : AbGroupEquiv G (coHomGr zero G A)
    fst H⁰conn' = isoToEquiv is
      where
      is : Iso _ _
      Iso.fun is = G→H⁰
      Iso.inv is = H⁰→G
      Iso.rightInv is = H⁰→G→H⁰
      Iso.leftInv is = G→H⁰→G
    snd H⁰conn' = makeIsGroupHom λ _ _ → refl

  H⁰conn : AbGroupEquiv (coHomGr zero G A) G
  H⁰conn = invGroupEquiv H⁰conn'

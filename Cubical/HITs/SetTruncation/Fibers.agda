{-

This file contains:

- Fibers of induced map between set truncations is the set truncation of fibers
  modulo a certain equivalence relation defined by π₁ of the base.

-}
module Cubical.HITs.SetTruncation.Fibers where

open import Cubical.HITs.SetTruncation.Base

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.HITs.SetTruncation as Set
open import Cubical.HITs.SetQuotients as SetQuot

open import Cubical.Relation.Binary

private
  variable
    ℓ ℓ' : Level

module _
  {X : Type ℓ }
  {Y : Type ℓ'}
  (f : X → Y) where

  private
    ∥f∥₂ : ∥ X ∥₂ → ∥ Y ∥₂
    ∥f∥₂ = Set.map f

  module _ (y : Y) where

    open Iso

    isSetFiber∥∥₂ : isSet (fiber ∥f∥₂ ∣ y ∣₂)
    isSetFiber∥∥₂ = isOfHLevelΣ 2 squash₂ (λ _ → isProp→isSet (squash₂ _ _))

    fiberRel : ∥ fiber f y ∥₂ → ∥ fiber f y ∥₂ → Type ℓ
    fiberRel a b = Set.map fst a ≡ Set.map fst b

    private
      proj : ∥ fiber f y ∥₂ / fiberRel → ∥ X ∥₂
      proj = SetQuot.rec squash₂ (Set.map fst) (λ _ _ p → p)

    ∥fiber∥₂/R→fiber∥∥₂ : ∥ fiber f y ∥₂ / fiberRel → fiber ∥f∥₂ ∣ y ∣₂
    ∥fiber∥₂/R→fiber∥∥₂ = SetQuot.rec isSetFiber∥∥₂ ∥fiber∥₂→fiber∥∥₂ feq
      where
      fiber→fiber∥∥₂ : fiber f y → fiber ∥f∥₂ ∣ y ∣₂
      fiber→fiber∥∥₂ (x , p) = ∣ x ∣₂ , cong ∣_∣₂ p

      ∥fiber∥₂→fiber∥∥₂ : ∥ fiber f y ∥₂ → fiber ∥f∥₂ ∣ y ∣₂
      ∥fiber∥₂→fiber∥∥₂ = Set.rec isSetFiber∥∥₂ fiber→fiber∥∥₂

      feq : (a b : ∥ fiber f y ∥₂) (r : fiberRel a b) → ∥fiber∥₂→fiber∥∥₂ a ≡ ∥fiber∥₂→fiber∥∥₂ b
      feq =
        Set.elim2 (λ _ _ → isProp→isSet (isPropΠ (λ _ → isSetFiber∥∥₂ _ _))) λ _ _ p →
        ΣPathP (p , isSet→isSet' squash₂ _ _ _ _)

    mereFiber→∥fiber∥₂/R : (x : X) → ∥ f x ≡ y ∥₁ → ∥ fiber f y ∥₂ / fiberRel
    mereFiber→∥fiber∥₂/R x = Prop.rec→Set squash/ (λ p → [ ∣ _ , p ∣₂ ]) (λ _ _ → eq/ _ _ refl)

    fiber∥∥₂→∥fiber∥₂/R : fiber ∥f∥₂ ∣ y ∣₂ → ∥ fiber f y ∥₂ / fiberRel
    fiber∥∥₂→∥fiber∥₂/R =
      uncurry
        (Set.elim (λ _ → isSetΠ λ _ → squash/) λ x p →
          mereFiber→∥fiber∥₂/R x (PathIdTrunc₀Iso .fun p))

    ∥fiber∥₂/R→fiber∥∥₂→fst : (q : ∥ fiber f y ∥₂ / fiberRel) → ∥fiber∥₂/R→fiber∥∥₂ q .fst ≡ proj q
    ∥fiber∥₂/R→fiber∥∥₂→fst =
      SetQuot.elimProp (λ _ → squash₂ _ _)
        (Set.elim (λ _ → isProp→isSet (squash₂ _ _)) (λ _ → refl))

    fiber∥∥₂→∥fiber∥₂/R→proj : (x : fiber ∥f∥₂ ∣ y ∣₂) → proj (fiber∥∥₂→∥fiber∥₂/R x) ≡ x .fst
    fiber∥∥₂→∥fiber∥₂/R→proj =
      uncurry
        (Set.elim (λ _ → isSetΠ λ _ → isProp→isSet (squash₂ _ _)) λ x p →
          Prop.elim {P = λ t → proj (mereFiber→∥fiber∥₂/R x t) ≡ ∣ x ∣₂}
            (λ _ → squash₂ _ _)
            (λ _ → refl)
            (PathIdTrunc₀Iso .fun p))

    ∥fiber∥₂/R→fiber∥∥₂→∥fiber∥₂/R :
      (x : ∥ fiber f y ∥₂ / fiberRel) → fiber∥∥₂→∥fiber∥₂/R (∥fiber∥₂/R→fiber∥∥₂ x) ≡ x
    ∥fiber∥₂/R→fiber∥∥₂→∥fiber∥₂/R =
      SetQuot.elimProp (λ _ → squash/ _ _)
        (Set.elim (λ _ → isProp→isSet (squash/ _ _))
          (λ _ → eq/ _ _ refl))

    fiber∥∥₂→∥fiber∥₂/R→fiber∥∥₂ :
      (x : fiber ∥f∥₂ ∣ y ∣₂) → ∥fiber∥₂/R→fiber∥∥₂ (fiber∥∥₂→∥fiber∥₂/R x) ≡ x
    fiber∥∥₂→∥fiber∥₂/R→fiber∥∥₂ x =
      Σ≡Prop
        (λ _ → squash₂ _ _)
        (∥fiber∥₂/R→fiber∥∥₂→fst (fiber∥∥₂→∥fiber∥₂/R x) ∙ fiber∥∥₂→∥fiber∥₂/R→proj x)

    Iso-∥fiber∥₂/R-fiber∥∥₂ : Iso (∥ fiber f y ∥₂ / fiberRel) (fiber ∥f∥₂ ∣ y ∣₂)
    Iso-∥fiber∥₂/R-fiber∥∥₂ .fun = ∥fiber∥₂/R→fiber∥∥₂
    Iso-∥fiber∥₂/R-fiber∥∥₂ .inv = fiber∥∥₂→∥fiber∥₂/R
    Iso-∥fiber∥₂/R-fiber∥∥₂ .leftInv = ∥fiber∥₂/R→fiber∥∥₂→∥fiber∥₂/R
    Iso-∥fiber∥₂/R-fiber∥∥₂ .rightInv = fiber∥∥₂→∥fiber∥₂/R→fiber∥∥₂

    -- main results

    ∥fiber∥₂/R≃fiber∥∥₂ : ∥ fiber f y ∥₂ / fiberRel ≃ fiber ∥f∥₂ ∣ y ∣₂
    ∥fiber∥₂/R≃fiber∥∥₂ = isoToEquiv Iso-∥fiber∥₂/R-fiber∥∥₂

    -- the relation is an equivalence relation

    open BinaryRelation
    open isEquivRel

    isEquivRelFiberRel : isEquivRel fiberRel
    isEquivRelFiberRel .reflexive _ = refl
    isEquivRelFiberRel .symmetric _ _ = sym
    isEquivRelFiberRel .transitive _ _ _ = _∙_

    -- alternative characterization of the relation in terms of equality in Y and fiber f y

    ∣transport∣ : ∥ y ≡ y ∥₂ → ∥ fiber f y ∥₂ → ∥ fiber f y ∥₂
    ∣transport∣ = Set.rec2 squash₂ (λ s (x , q) → ∣ x , q ∙ s ∣₂)

    fiberRel2 : (x x' : ∥ fiber f y ∥₂) → Type (ℓ-max ℓ ℓ')
    fiberRel2 x x' = ∥ Σ[ s ∈ ∥ y ≡ y ∥₂ ] ∣transport∣ s x ≡ x' ∥₁

    fiberRel2→1 : ∀ x x' → fiberRel2 x x' → fiberRel x x'
    fiberRel2→1 =
      Set.elim2 (λ _ _ → isSetΠ λ _ → isOfHLevelPath 2 squash₂ _ _) λ _ _ →
      Prop.rec (squash₂ _ _)
        (uncurry
          (Set.elim (λ _ → isSetΠ λ _ → isOfHLevelPath 2 squash₂ _ _) λ _ →
            cong (Set.map fst)))

    fiberRel1→2 : ∀ x x' → fiberRel x x' → fiberRel2 x x'
    fiberRel1→2 =
      Set.elim2 (λ _ _ → isSetΠ λ _ → isProp→isSet squash₁) λ a b p →
      Prop.rec squash₁
        (λ q →
          let
            filler = doubleCompPath-filler (sym (a .snd)) (cong f q) (b .snd)
          in
            ∣ ∣ filler i1 ∣₂ , cong ∣_∣₂ (ΣPathP (q , adjustLemma (flipSquare filler))) ∣₁)
        (PathIdTrunc₀Iso .Iso.fun p)
      where
      adjustLemma : {x y z w : Y} {p : x ≡ y} {q : x ≡ z} {r : z ≡ w} {s : y ≡ w}
        → PathP (λ i → p i ≡ r i) q s
        → PathP (λ i → p i ≡ w) (q ∙ r) s
      adjustLemma {p = p} {q} {r} {s} α i j =
        hcomp
          (λ k → λ
            { (i = i0) → compPath-filler q r k j
            ; (i = i1) → s j
            ; (j = i0) → p i
            ; (j = i1) → r (i ∨ k)})
          (α i j)

    fiberRel1≃2 : ∀ x x' → fiberRel x x' ≃ fiberRel2 x x'
    fiberRel1≃2 _ _ =
      propBiimpl→Equiv (squash₂ _ _) squash₁ (fiberRel1→2 _ _) (fiberRel2→1 _ _)

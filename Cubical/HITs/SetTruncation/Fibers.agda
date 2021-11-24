{-

This file contains:

- Fibers of induced map between set truncations is the set truncation of fibers
  modulo a certain equivalence relation defined by π₁ of the base.

-}
{-# OPTIONS --safe #-}
module Cubical.HITs.SetTruncation.Fibers where

open import Cubical.HITs.SetTruncation.Base

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.HITs.SetTruncation as Set
open import Cubical.HITs.SetQuotients as SetQuot

open import Cubical.Relation.Binary

private
  variable
    ℓ ℓ' : Level

module _
  (X : Type ℓ )
  (Y : Type ℓ')
  (f : X → Y) where

  private
    ∥f∥₂ : ∥ X ∥₂ → ∥ Y ∥₂
    ∥f∥₂ = Set.map f

  module _
    (y : Y) where

    open Iso

    fiber→fiber∥∥₂ : fiber f y → fiber ∥f∥₂ ∣ y ∣₂
    fiber→fiber∥∥₂ (x , p) = ∣ x ∣₂ , cong ∣_∣₂ p

    isSetFiber∥∥₂ : isSet (fiber ∥f∥₂ ∣ y ∣₂)
    isSetFiber∥∥₂ = isOfHLevelΣ 2 squash₂ (λ _ → isProp→isSet (squash₂ _ _))

    ∥fiber∥₂→fiber∥∥₂ : ∥ fiber f y ∥₂ → fiber ∥f∥₂ ∣ y ∣₂
    ∥fiber∥₂→fiber∥∥₂ = Set.rec isSetFiber∥∥₂ fiber→fiber∥∥₂

    ∣transport∣ : ∥ y ≡ y ∥₂ → ∥ fiber f y ∥₂ → ∥ fiber f y ∥₂
    ∣transport∣ = Set.rec2 squash₂ (λ s (x , q) → ∣ x , q ∙ s ∣₂)

    fiberRel2 : ∥ fiber f y ∥₂ → ∥ fiber f y ∥₂ → Type (ℓ-max ℓ ℓ')
    fiberRel2 x x' =
      ∥ Σ[ s ∈ ∥ y ≡ y ∥₂ ] ∣transport∣ s x ≡ x' ∥

    fiberRel' : fiber f y → fiber f y → Type (ℓ-max ℓ ℓ')
    fiberRel' (x , p) (x' , p') =
      Σ[ s ∈ y ≡ y ] Σ[ q ∈ x ≡ x' ] PathP (λ i → f (q i) ≡ s i) p p'

    feq' : (a b : fiber f y)(r : fiberRel' a b) → fiber→fiber∥∥₂ a ≡ fiber→fiber∥∥₂ b
    feq' (x , p) (x' , p') (s , q , t) i .fst = ∣ q i ∣₂
    feq' (x , p) (x' , p') (s , q , t) i .snd j =
      hcomp (λ k → λ { (i = i0) → ∣ p  j ∣₂
                     ; (i = i1) → ∣ p' j ∣₂
                     ; (j = i0) → ∣ f (q i) ∣₂
                     ; (j = i1) → squash₂ ∣ y ∣₂ ∣ y ∣₂ (cong ∣_∣₂ s) refl k i })
            (∣ t i j ∣₂)

    fiberRel : ∥ fiber f y ∥₂ → ∥ fiber f y ∥₂ → Type (ℓ-max ℓ ℓ')
    fiberRel a b = Set.rec2 isSetHProp (λ a b → ∥ fiberRel' a b ∥ , isPropPropTrunc) a b .fst

    isPropFiberRel : (x x' : ∥ fiber f y ∥₂) → isProp (fiberRel x x')
    isPropFiberRel a b = Set.rec2 isSetHProp (λ a b → ∥ fiberRel' a b ∥ , isPropPropTrunc) a b .snd

    fiberRel'→fiberRel2' : ((x , p) x' : fiber f y) → fiberRel' (x , p) x' → Σ[ s ∈ y ≡ y ] (x , p ∙ s) ≡ x'
    fiberRel'→fiberRel2' _ _ (_ , _ , t) .fst i = t i i1
    fiberRel'→fiberRel2' _ _ (_ , q , _) .snd i .fst = q i
    fiberRel'→fiberRel2' (x , p) (x' , p') (s , q , t) .snd i .snd j =
      hcomp (λ k → λ { (i = i0) → compPath-filler p s k j
                     ; (i = i1) → p' j
                     ; (j = i0) → f (q i)
                     ; (j = i1) → s (i ∨ k) })
            (t i j)

    truncRel : ((x , p) x' : fiber f y) → Σ[ s ∈ y ≡ y ] (x , p ∙ s) ≡ x'
      → ∥ Σ[ s ∈ ∥ y ≡ y ∥₂ ] ∣transport∣ s ∣ x , p ∣₂ ≡ ∣ x' ∣₂ ∥
    truncRel _ _ (s , p) = ∣ ∣ s ∣₂ , cong ∣_∣₂ p ∣

    truncRel` : ((x , p) x' : fiber f y) → ∥ Σ[ s ∈ y ≡ y ] (x , p ∙ s) ≡ x' ∥
      → ∥ Σ[ s ∈ ∥ y ≡ y ∥₂ ] ∣transport∣ s ∣ x , p ∣₂ ≡ ∣ x' ∣₂ ∥
    truncRel` x x' = Prop.rec isPropPropTrunc (λ r → truncRel x x' r)

    fiberRel→fiberRel2' : (x x' : fiber f y) → fiberRel ∣ x ∣₂ ∣ x' ∣₂ → fiberRel2 ∣ x ∣₂ ∣ x' ∣₂
    fiberRel→fiberRel2' x x' = Prop.rec isPropPropTrunc (λ r → truncRel x x' (fiberRel'→fiberRel2' x x' r))

    fiberRel→fiberRel2 : (x x' : ∥ fiber f y ∥₂) → fiberRel x x' → fiberRel2 x x'
    fiberRel→fiberRel2 =
      Set.elim2 (λ _ _ → isProp→isSet (isPropΠ (λ _ → isPropPropTrunc)))
        (λ x x' → fiberRel→fiberRel2' x x')

    truncRel'' : ((x , p) x' : fiber f y) → (s : y ≡ y) → ∣ x , p ∙ s ∣₂ ≡ ∣ x' ∣₂
      → ∥ (x , p ∙ s) ≡ x' ∥
    truncRel'' _ _ _ q = Set.PathIdTrunc₀Iso .fun q

    truncRel''' : ((x , p) x' : fiber f y) → (s : ∥ y ≡ y ∥₂) → ∣transport∣ s ∣ x , p ∣₂ ≡ ∣ x' ∣₂
      → ∥ Σ[ s ∈ y ≡ y ] ∥ (x , p ∙ s) ≡ x' ∥ ∥
    truncRel''' x x' =
      Set.elim (λ _ → isProp→isSet (isPropΠ (λ _ → isPropPropTrunc)))
        (λ s' p' → ∣ s' , truncRel'' x x' s' p' ∣)

    helper-fun : ((x , p) x' : fiber f y) → (s : y ≡ y)
      → ∥ (x , p ∙ s) ≡ x' ∥ → ∥ Σ[ s ∈ y ≡ y ] (x , p ∙ s) ≡ x' ∥
    helper-fun _ _ s = Prop.rec isPropPropTrunc (λ q → ∣ s , q ∣)

    helper-fun' : ((x , p) x' : fiber f y) → ∥ Σ[ s ∈ y ≡ y ] ∥ (x , p ∙ s) ≡ x' ∥ ∥
      → ∥ Σ[ s ∈ y ≡ y ] (x , p ∙ s) ≡ x' ∥
    helper-fun' _ _ =
      Prop.rec isPropPropTrunc (λ (s , q) → helper-fun _ _ s q)

    truncRel' : ((x , p) x' : fiber f y) → ∥ Σ[ s ∈ ∥ y ≡ y ∥₂ ] ∣transport∣ s ∣ x , p ∣₂ ≡ ∣ x' ∣₂ ∥
      → ∥ Σ[ s ∈ y ≡ y ] (x , p ∙ s) ≡ x' ∥
    truncRel' _ _ = Prop.rec isPropPropTrunc (λ (s , q) → helper-fun' _ _ (truncRel''' _ _ s q))

    fiberRel2'→fiberRel' : ((x , p) x' : fiber f y) → (s : y ≡ y)(t : (x , p ∙ s) ≡ x') → fiberRel' (x , p) x'
    fiberRel2'→fiberRel' _ _ s _ .fst = s
    fiberRel2'→fiberRel' _ _ _ t .snd .fst i = t i .fst
    fiberRel2'→fiberRel' (x , p) (x' , p') s t .snd .snd i j =
      hcomp (λ k → λ { (i = i0) → compPath-filler p s (~ k) j
                     ; (i = i1) → t k .snd j
                     ; (j = i0) → f (t (i ∧ k) .fst)
                     ; (j = i1) → s (i ∨ (~ k)) })
            ((p ∙ s) j)

    fiberRel2'→fiberRel'-helper : ((x , p) x' : fiber f y)
      → ∥ Σ[ s ∈ y ≡ y ] (x , p ∙ s) ≡ x' ∥ → fiberRel ∣ x , p ∣₂ ∣ x' ∣₂
    fiberRel2'→fiberRel'-helper _ _ =
      Prop.rec isPropPropTrunc (λ (s , p) → ∣ fiberRel2'→fiberRel' _ _ s p ∣)

    fiberRel2→fiberRel : (x x' : ∥ fiber f y ∥₂) → fiberRel2 x x' → fiberRel x x'
    fiberRel2→fiberRel =
      Set.elim2 (λ x x' → isProp→isSet (isPropΠ (λ _ → isPropFiberRel x x')))
        (λ _ _ r → fiberRel2'→fiberRel'-helper _ _ (truncRel' _ _ r))

    fiberRel≃fiberRel2 : (x x' : ∥ fiber f y ∥₂) → fiberRel x x' ≃ fiberRel2 x x'
    fiberRel≃fiberRel2 x x' =
      propBiimpl→Equiv (isPropFiberRel x x') isPropPropTrunc
        (fiberRel→fiberRel2 _ _) (fiberRel2→fiberRel _ _)

    feq'' : (a b : fiber f y)(r : fiberRel ∣ a ∣₂ ∣ b ∣₂) → ∥fiber∥₂→fiber∥∥₂ ∣ a ∣₂ ≡ ∥fiber∥₂→fiber∥∥₂ ∣ b ∣₂
    feq'' a b r = Prop.rec (isSetFiber∥∥₂ _ _) (feq' a b) r

    feq : (a b : ∥ fiber f y ∥₂)(r : fiberRel a b) → ∥fiber∥₂→fiber∥∥₂ a ≡ ∥fiber∥₂→fiber∥∥₂ b
    feq = Set.elim2 (λ _ _ → isProp→isSet (isPropΠ (λ _ → isSetFiber∥∥₂ _ _))) feq''

    ∥fiber∥₂/R→fiber∥∥₂ : ∥ fiber f y ∥₂ / fiberRel → fiber ∥f∥₂ ∣ y ∣₂
    ∥fiber∥₂/R→fiber∥∥₂ = SetQuot.rec isSetFiber∥∥₂ ∥fiber∥₂→fiber∥∥₂ feq

    fun1 : (x x' : X)(q : x ≡ x')(p : f x ≡ y)(p' : f x' ≡ y) → fiberRel' (x , p) (x' , p')
    fun1 x x' q p p' .fst = (sym p) ∙∙ cong f q ∙∙ p'
    fun1 x x' q p p' .snd .fst = q
    fun1 x x' q p p' .snd .snd i j = doubleCompPath-filler (sym p) (cong f q) p' j i

    fun2'' : (x : X) → (p p' : f x ≡ y) → fiberRel ∣ x , p ∣₂ ∣ x , p' ∣₂
    fun2'' x p p' = ∣ fun1 x x refl p p' ∣

    fun2' : (x : X) → (p : ∥ f x ≡ y ∥) → ∥ fiber f y ∥₂ / fiberRel
    fun2' x = Prop.rec→Set squash/ (λ p → [ ∣ x , p ∣₂ ]) (λ p p' → eq/ _ _ (fun2'' x p p'))

    fun3' : (x : X) → (p : ∥f∥₂ ∣ x ∣₂ ≡ ∣ y ∣₂) → ∥ fiber f y ∥₂ / fiberRel
    fun3' x p = fun2' x (Set.PathIdTrunc₀Iso .fun p)

    fun3 : (x : ∥ X ∥₂) → (p : ∥f∥₂ x ≡ ∣ y ∣₂) → ∥ fiber f y ∥₂ / fiberRel
    fun3 = Set.elim (λ _ → isSetΠ (λ _ → squash/)) fun3'

    fiber∥∥₂→∥fiber∥₂/R : fiber ∥f∥₂ ∣ y ∣₂ → ∥ fiber f y ∥₂ / fiberRel
    fiber∥∥₂→∥fiber∥₂/R (x , p) = fun3 x p

    leftHtpy : (x : fiber f y) → fiber∥∥₂→∥fiber∥₂/R (fiber→fiber∥∥₂ x) ≡ [ ∣ x ∣₂ ]
    leftHtpy (x , p) = eq/ _ _ (fun2'' x _ _)

    ∥fiber∥₂/R→fiber∥∥₂→∥fiber∥₂/R :
      (x : ∥ fiber f y ∥₂ / fiberRel) → fiber∥∥₂→∥fiber∥₂/R (∥fiber∥₂/R→fiber∥∥₂ x) ≡ x
    ∥fiber∥₂/R→fiber∥∥₂→∥fiber∥₂/R = SetQuot.elimProp (λ _ → squash/ _ _) (Set.elim (λ _ → isProp→isSet (squash/ _ _)) leftHtpy)

    rightHtpy :
      (x : X) → (p : f x ≡ y) → ∥fiber∥₂/R→fiber∥∥₂ (fun2' x ∣ p ∣) ≡ (∣ x ∣₂ , (Set.PathIdTrunc₀Iso .inv ∣ p ∣))
    rightHtpy x p i .fst = ∣ x ∣₂
    rightHtpy x p i .snd =
      isOfHLevelRespectEquiv 1 (invEquiv (isoToEquiv (PathIdTrunc₀Iso))) isPropPropTrunc
        (∥fiber∥₂/R→fiber∥∥₂ (fun2' x ∣ p ∣) .snd) (Set.PathIdTrunc₀Iso .inv ∣ p ∣) i

    rightHtpy' :
      (x : X) → (p : ∥ f x ≡ y ∥) → ∥fiber∥₂/R→fiber∥∥₂ (fun2' x p) ≡ (∣ x ∣₂ , (Set.PathIdTrunc₀Iso .inv p))
    rightHtpy' x = Prop.elim (λ _ → isSetFiber∥∥₂ _ _) (rightHtpy x)

    rightHtpy'' :
      (x : X) → (p : ∥f∥₂ ∣ x ∣₂ ≡ ∣ y ∣₂) → ∥fiber∥₂/R→fiber∥∥₂ (fun3' x p) ≡ (∣ x ∣₂ , p)
    rightHtpy'' x p i .fst = rightHtpy' x (Set.PathIdTrunc₀Iso .fun p) i .fst
    rightHtpy'' x p i .snd =
      hcomp (λ j → λ { (i = i0) → rightHtpy' x (Set.PathIdTrunc₀Iso .fun p) i0 .snd
                     ; (i = i1) → Set.PathIdTrunc₀Iso .leftInv p j })
            (rightHtpy' x (Set.PathIdTrunc₀Iso .fun p) i .snd)

    rightHtpy''' :
      (x : ∥ X ∥₂) → (p : ∥f∥₂ x ≡ ∣ y ∣₂) → ∥fiber∥₂/R→fiber∥∥₂ (fiber∥∥₂→∥fiber∥₂/R (x , p)) ≡ (x , p)
    rightHtpy''' = Set.elim (λ _ → isSetΠ (λ _ → isProp→isSet (isSetFiber∥∥₂ _ _))) rightHtpy''

    fiber∥∥₂→∥fiber∥₂/R→fiber∥∥₂ :
      (x : fiber ∥f∥₂ ∣ y ∣₂) → ∥fiber∥₂/R→fiber∥∥₂ (fiber∥∥₂→∥fiber∥₂/R x) ≡ x
    fiber∥∥₂→∥fiber∥₂/R→fiber∥∥₂ (x , p) = rightHtpy''' x p

    Iso-∥fiber∥₂/R-fiber∥∥₂ : Iso (∥ fiber f y ∥₂ / fiberRel) (fiber ∥f∥₂ ∣ y ∣₂)
    Iso-∥fiber∥₂/R-fiber∥∥₂ .fun = ∥fiber∥₂/R→fiber∥∥₂
    Iso-∥fiber∥₂/R-fiber∥∥₂ .inv = fiber∥∥₂→∥fiber∥₂/R
    Iso-∥fiber∥₂/R-fiber∥∥₂ .leftInv = ∥fiber∥₂/R→fiber∥∥₂→∥fiber∥₂/R
    Iso-∥fiber∥₂/R-fiber∥∥₂ .rightInv = fiber∥∥₂→∥fiber∥₂/R→fiber∥∥₂

    -- main results

    ∥fiber∥₂/R≃fiber∥∥₂ : ∥ fiber f y ∥₂ / fiberRel ≃ fiber ∥f∥₂ ∣ y ∣₂
    ∥fiber∥₂/R≃fiber∥∥₂ = isoToEquiv Iso-∥fiber∥₂/R-fiber∥∥₂

    ∥fiber∥₂/Rel≃∥fiber∥₂/R : ∥ fiber f y ∥₂ / fiberRel2 ≃ ∥ fiber f y ∥₂ / fiberRel
    ∥fiber∥₂/Rel≃∥fiber∥₂/R =
      isoToEquiv (relBiimpl→TruncIso
        (λ {a} {b} → fiberRel2→fiberRel a b)
        (λ {a} {b} → fiberRel→fiberRel2 a b))

    ∥fiber∥₂/Rel≃fiber∥∥₂ : ∥ fiber f y ∥₂ / fiberRel2 ≃ fiber ∥f∥₂ ∣ y ∣₂
    ∥fiber∥₂/Rel≃fiber∥∥₂ = compEquiv ∥fiber∥₂/Rel≃∥fiber∥₂/R ∥fiber∥₂/R≃fiber∥∥₂

    -- the relation is equivalence relation

    open BinaryRelation

    isReflFiberRel' : (x : fiber f y) → fiberRel2 ∣ x ∣₂ ∣ x ∣₂
    isReflFiberRel' (x , q) = ∣ ∣ refl ∣₂ , (λ i → ∣ x , rUnit q (~ i) ∣₂) ∣

    isReflFiberRel : isRefl fiberRel2
    isReflFiberRel = Set.elim (λ _ → isProp→isSet isPropPropTrunc) isReflFiberRel'

    isSymFiberRel'' : ((x , p) (x' , p') : fiber f y)
      → Σ[ s ∈ y ≡ y ] (x , p ∙ s) ≡ (x' , p') → Σ[ s' ∈ y ≡ y ] (x' , p' ∙ s') ≡ (x , p)
    isSymFiberRel'' _ _ (s , _) .fst = sym s
    isSymFiberRel'' (x , p) (x' , p') (s , q) .snd i .fst = q (~ i) .fst
    isSymFiberRel'' (x , p) (x' , p') (s , q) .snd i .snd j =
      hcomp (λ k → λ { (i = i0) → compPath-filler p' (sym s) k j
                     ; (i = i1) → compPath-filler p s (~ k) j
                     ; (j = i0) → f (q (~ i) .fst)
                     ; (j = i1) → s (~ k) })
            (q (~ i) .snd j)

    isSymFiberRel' : (x x' : fiber f y)
      → fiberRel2 ∣ x ∣₂ ∣ x' ∣₂ → fiberRel2 ∣ x' ∣₂ ∣ x ∣₂
    isSymFiberRel' _ _ = truncRel` _ _ ∘ Prop.rec isPropPropTrunc (λ r → ∣ isSymFiberRel'' _ _ r ∣) ∘ truncRel' _ _

    isSymFiberRel : isSym fiberRel2
    isSymFiberRel = Set.elim2 (λ _ _ → isProp→isSet (isPropΠ (λ _ → isPropPropTrunc))) isSymFiberRel'

    isTransFiberRel'' : ((x , p) (x' , p') (x'' , p'') : fiber f y)
      → Σ[ s ∈ y ≡ y ] (x , p ∙ s) ≡ (x' , p') → Σ[ s' ∈ y ≡ y ] (x' , p' ∙ s') ≡ (x'' , p'')
      → Σ[ s'' ∈ y ≡ y ] (x , p ∙ s'') ≡ (x'' , p'')
    isTransFiberRel'' (x , p) (x' , p') (x'' , p'') (s , q) (s' , q') =
      let sq : (i j : I) → Y
          sq i j =
            hcomp (λ k → λ { (i = i0) → p j
                           ; (i = i1) → fiberRel2'→fiberRel' _ _ s' q' .snd .snd k j
                           ; (j = i0) → f (compPath-filler (cong fst q) (cong fst q') k i)
                           ; (j = i1) → compPath-filler s s' k i })
                  (fiberRel2'→fiberRel' _ _ s q .snd .snd i j)
      in  fiberRel'→fiberRel2' _ _ (_ , _ , (λ i j → sq i j))

    isTransFiberRel' : (x x' x'' : fiber f y)
      → fiberRel2 ∣ x ∣₂ ∣ x' ∣₂ → fiberRel2 ∣ x' ∣₂ ∣ x'' ∣₂ → fiberRel2 ∣ x ∣₂ ∣ x'' ∣₂
    isTransFiberRel' _ _ _ a b =
      truncRel` _ _ (Prop.rec2 isPropPropTrunc
        (λ r r' → ∣ isTransFiberRel'' _ _ _ r r' ∣) (truncRel' _ _ a) (truncRel' _ _ b))

    isTransFiberRel : isTrans fiberRel2
    isTransFiberRel =
      Set.elim3 (λ _ _ _ → isProp→isSet (isPropΠ2 (λ _ _ → isPropPropTrunc))) isTransFiberRel'

    open isEquivRel

    isEquivRelFiberRel : isEquivRel fiberRel2
    isEquivRelFiberRel .reflexive = isReflFiberRel
    isEquivRelFiberRel .symmetric = isSymFiberRel
    isEquivRelFiberRel .transitive = isTransFiberRel

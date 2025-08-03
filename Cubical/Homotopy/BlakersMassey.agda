{-

A Cubical proof of Blakers-Massey Theorem (KANG Rongji, Oct. 2021)

Based on the previous type-theoretic proof described in
  Kuen-Bang Hou (Favonia), Eric Finster, Dan Licata, Peter LeFanu Lumsdaine,
  "A Mechanization of the Blakers–Massey Connectivity Theorem in Homotopy Type Theory"
  (https://arxiv.org/abs/1605.03227)

Also the HoTT-Agda formalization by Favonia:
  (https://github.com/HoTT/HoTT-Agda/blob/master/theorems/homotopy/BlakersMassey.agda)

Using cubes explicitly as much as possible.

-}
{-# OPTIONS  #-}
module Cubical.Homotopy.BlakersMassey where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Transport
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Pointed

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open Iso
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv.HalfAdjoint

open import Cubical.Data.Nat hiding (elim)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.HITs.Truncation renaming (hLevelTrunc to Trunc)
open import Cubical.HITs.Pushout hiding (PushoutGenFib)
open import Cubical.HITs.Wedge

open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.WedgeConnectivity

module BlakersMassey {ℓ₁ ℓ₂ ℓ₃ : Level}
  (X : Type ℓ₁)(Y : Type ℓ₂)(Q : X → Y → Type ℓ₃)
  {m : HLevel} (leftConn  : (x : X) → isConnected (1 + m) (Σ[ y ∈ Y ] Q x y))
  {n : HLevel} (rightConn : (y : Y) → isConnected (1 + n) (Σ[ x ∈ X ] Q x y))
  where

  ℓ : Level
  ℓ = ℓ-max (ℓ-max ℓ₁ ℓ₂) ℓ₃

  leftFiber  : X → Type (ℓ-max ℓ₂ ℓ₃)
  leftFiber x  = Σ[ y ∈ Y ] Q x y

  rightFiber : Y → Type (ℓ-max ℓ₁ ℓ₃)
  rightFiber y = Σ[ x ∈ X ] Q x y

  {- We use the alternative formulation of pushout with fewer parameters -}

  PushoutQ = PushoutGen Q

  {- Some preliminary definitions for convenience -}

  fiberSquare :
      {x₀ x₁ : X}{y₀ : Y}{p : PushoutQ}(q₀₀ : Q x₀ y₀)(q₁₀ : Q x₁ y₀)
    → inl x₁ ≡ p → inl x₀ ≡ p → Type ℓ
  fiberSquare q₀₀ q₁₀ r' r = PathP (λ i → push q₀₀ (~ i) ≡ r' i) (sym (push q₁₀)) r

  fiberSquarePush :
      {x₀ x₁ : X}{y₀ y₁ : Y}(q₀₀ : Q x₀ y₀)(q₁₀ : Q x₁ y₀)(q₁₁ : Q x₁ y₁)
    → inl x₀ ≡ inr y₁ → Type ℓ
  fiberSquarePush q₀₀ q₁₀ q₁₁ = fiberSquare q₀₀ q₁₀ (push q₁₁)

  fiber' : {x₀ : X}{y₀ : Y}(q₀₀ : Q x₀ y₀){x₁ : X}{p : PushoutQ} → inl x₁ ≡ p → inl x₀ ≡ p → Type ℓ
  fiber' {y₀ = y₀} q₀₀ {x₁ = x₁} r' r = Σ[ q₁₀ ∈ Q x₁ y₀ ] fiberSquare q₀₀ q₁₀ r' r

  fiber'Push : {x₀ x₁ : X}{y₀ y₁ : Y}(q₀₀ : Q x₀ y₀)(q₁₁ : Q x₁ y₁) → inl x₀ ≡ inr y₁ → Type ℓ
  fiber'Push q₀₀ q₁₁ = fiber' q₀₀ (push q₁₁)

  leftCodeExtended :
      {x₀ : X}{y₀ : Y}(q₀₀ : Q x₀ y₀)
    → (x₁ : X){p : PushoutQ} → inl x₁ ≡ p → inl x₀ ≡ p → Type ℓ
  leftCodeExtended {y₀ = y₀} q₀₀ x₁ r' r = Trunc (m + n) (fiber' q₀₀ r' r)

  rightCode : {x₀ : X}(y : Y) → Path PushoutQ (inl x₀) (inr y) → Type ℓ
  rightCode y r = Trunc (m + n) (fiber push r)

  {- Bunch of coherence data that will be used to construct Code -}

  {- Definitions of fiber→ -}

  module _
    {x₁ : X}{y₀ : Y}(q₁₀ : Q x₁ y₀) where

    {- (x₀ , q₀₀) = (x₁ , q₁₀) -}
    module _
      {y₁ : Y}(q₁₁ : Q x₁ y₁)
      (r : inl x₁ ≡ inr y₁)
      (p : fiberSquarePush q₁₀ q₁₀ q₁₁ r) where

      fiber→[q₀₀=q₁₀]-filler : (i j k : I) → PushoutQ
      fiber→[q₀₀=q₁₀]-filler i j k' =
        hfill (λ k → λ { (i = i0) → push q₁₁ (j ∧ k)
                       ; (i = i1) → p k j
                       ; (j = i0) → push q₁₀ (i ∧ ~ k)
                       ; (j = i1) → push q₁₁ k })
              (inS (push q₁₀ (i ∧ ~ j))) k'

      fiber→[q₀₀=q₁₀] : fiber push r
      fiber→[q₀₀=q₁₀] .fst = q₁₁
      fiber→[q₀₀=q₁₀] .snd i j = fiber→[q₀₀=q₁₀]-filler i j i1

      ∣fiber→[q₀₀=q₁₀]∣ : rightCode _ r
      ∣fiber→[q₀₀=q₁₀]∣ = ∣ fiber→[q₀₀=q₁₀] ∣ₕ

    {- (y₁ , q₁₁) = (y₀ , q₁₀) -}
    module _
      {x₀ : X}(q₀₀ : Q x₀ y₀)
      (r : inl x₀ ≡ inr y₀)
      (p : fiberSquarePush q₀₀ q₁₀ q₁₀ r) where

      fiber→[q₁₁=q₁₀]-filler : (i j k : I) → PushoutQ
      fiber→[q₁₁=q₁₀]-filler i j k' =
        hfill (λ k → λ { (i = i0) → push q₀₀ (j ∨ ~ k)
                       ; (i = i1) → p k j
                       ; (j = i0) → push q₀₀ (~ k)
                       ; (j = i1) → push q₁₀ (~ i ∨ k) })
              (inS (push q₁₀ (~ i ∨ ~ j))) k'

      fiber→[q₁₁=q₁₀] : fiber push r
      fiber→[q₁₁=q₁₀] .fst = q₀₀
      fiber→[q₁₁=q₁₀] .snd i j = fiber→[q₁₁=q₁₀]-filler i j i1

      ∣fiber→[q₁₁=q₁₀]∣ : rightCode _ r
      ∣fiber→[q₁₁=q₁₀]∣ = ∣ fiber→[q₁₁=q₁₀] ∣ₕ

    {- q₀₀ = q₁₁ = q₁₀ -}
    fiber→[q₀₀=q₁₀=q₁₁]-filler :
        (r : inl x₁ ≡ inr y₀)
      → (p : fiberSquarePush q₁₀ q₁₀ q₁₀ r)
      → (i j k l : I) → PushoutQ
    fiber→[q₀₀=q₁₀=q₁₁]-filler r p i j k l' =
      hfill (λ l → λ { (i = i0) → fiber→[q₀₀=q₁₀]-filler q₁₀ r p j k l
                     ; (i = i1) → fiber→[q₁₁=q₁₀]-filler q₁₀ r p j k l
                     ; (j = i0) → push q₁₀ ((i ∨ (k ∧ l)) ∧ (k ∨ (i ∧ ~ l)))
                     ; (j = i1) → p l k
                     ; (k = i0) → push q₁₀ ((i ∨ j) ∧ ~ l)
                     ; (k = i1) → push q₁₀ ((i ∧ ~ j) ∨ l) })
            (inS (push q₁₀ ((i ∨ (~ k ∧ j)) ∧ (~ k ∨ (i ∧ ~ j))))) l'

    fiber→[q₀₀=q₁₀=q₁₁] : fiber→[q₀₀=q₁₀] q₁₀ ≡ fiber→[q₁₁=q₁₀] q₁₀
    fiber→[q₀₀=q₁₀=q₁₁] i r p .fst = q₁₀
    fiber→[q₀₀=q₁₀=q₁₁] i r p .snd j k = fiber→[q₀₀=q₁₀=q₁₁]-filler r p i j k i1

    ∣fiber→[q₀₀=q₁₀=q₁₁]∣ : ∣fiber→[q₀₀=q₁₀]∣ q₁₀ ≡ ∣fiber→[q₁₁=q₁₀]∣ q₁₀
    ∣fiber→[q₀₀=q₁₀=q₁₁]∣ i r p = ∣ fiber→[q₀₀=q₁₀=q₁₁] i r p ∣ₕ

  {- Definitions of fiber← -}

  module _
    {x₀ : X}{y₁ : Y}(q₀₁ : Q x₀ y₁) where

    {- (x₁ , q₁₁) = (x₀ , q₀₁) -}
    module _
      {y₀ : Y}(q₀₀ : Q x₀ y₀)
      (r : inl x₀ ≡ inr y₁)
      (p : push q₀₁ ≡ r) where

      fiber←[q₁₁=q₀₁]-filler : (i j k : I) → PushoutQ
      fiber←[q₁₁=q₀₁]-filler i j k' =
        hfill (λ k → λ { (i = i0) → push q₀₀ (~ j ∧ k)
                       ; (i = i1) → p k j
                       ; (j = i0) → push q₀₀ (~ i ∧ k)
                       ; (j = i1) → push q₀₁ i })
              (inS (push q₀₁ (i ∧ j))) k'

      fiber←[q₁₁=q₀₁] : fiber'Push  q₀₀ q₀₁ r
      fiber←[q₁₁=q₀₁] .fst = q₀₀
      fiber←[q₁₁=q₀₁] .snd i j = fiber←[q₁₁=q₀₁]-filler i j i1

      ∣fiber←[q₁₁=q₀₁]∣ : leftCodeExtended q₀₀ _ (push q₀₁) r
      ∣fiber←[q₁₁=q₀₁]∣ = ∣ fiber←[q₁₁=q₀₁] ∣ₕ

    {- (y₀ , q₀₀) = (y₁ , q₀₁) -}
    module _
      {x₁ : X}(q₁₁ : Q x₁ y₁)
      (r : inl x₀ ≡ inr y₁)
      (p : push q₀₁ ≡ r) where

      fiber←[q₀₀=q₀₁]-filler : (i j k : I) → PushoutQ
      fiber←[q₀₀=q₀₁]-filler i j k' =
        hfill (λ k → λ { (i = i0) → push q₁₁ (~ j ∨ ~ k)
                       ; (i = i1) → p k j
                       ; (j = i0) → push q₀₁ (~ i)
                       ; (j = i1) → push q₁₁ (i ∨ ~ k) })
              (inS (push q₀₁ (~ i ∨ j))) k'

      fiber←[q₀₀=q₀₁] : fiber'Push q₀₁ q₁₁ r
      fiber←[q₀₀=q₀₁] .fst = q₁₁
      fiber←[q₀₀=q₀₁] .snd i j = fiber←[q₀₀=q₀₁]-filler i j i1

      ∣fiber←[q₀₀=q₀₁]∣ : leftCodeExtended q₀₁ _ (push q₁₁) r
      ∣fiber←[q₀₀=q₀₁]∣ = ∣ fiber←[q₀₀=q₀₁] ∣ₕ

    {- q₀₀ = q₀₁ = q₁₁ -}
    fiber←[q₀₀=q₀₁=q₁₁]-filler :
        (r : inl x₀ ≡ inr y₁)
      → (p : push q₀₁ ≡ r)
      → (i j k l : I) → PushoutQ
    fiber←[q₀₀=q₀₁=q₁₁]-filler r p i j k l' =
      hfill (λ l → λ { (i = i0) → fiber←[q₁₁=q₀₁]-filler q₀₁ r p j k l
                     ; (i = i1) → fiber←[q₀₀=q₀₁]-filler q₀₁ r p j k l
                     ; (j = i0) → push q₀₁ ((i ∨ (~ k ∧ l)) ∧ (~ k ∨ (i ∧ ~ l)))
                     ; (j = i1) → p l k
                     ; (k = i0) → push q₀₁ ((i ∨ l) ∧ ~ j)
                     ; (k = i1) → push q₀₁ ((i ∧ ~ l) ∨ j) })
            (inS (push q₀₁ ((i ∨ (k ∧ j)) ∧ (k ∨ (i ∧ ~ j))))) l'

    fiber←[q₀₀=q₀₁=q₁₁] : fiber←[q₁₁=q₀₁] q₀₁ ≡ fiber←[q₀₀=q₀₁] q₀₁
    fiber←[q₀₀=q₀₁=q₁₁] i r p .fst = q₀₁
    fiber←[q₀₀=q₀₁=q₁₁] i r p .snd j k = fiber←[q₀₀=q₀₁=q₁₁]-filler r p i j k i1

    ∣fiber←[q₀₀=q₀₁=q₁₁]∣ : ∣fiber←[q₁₁=q₀₁]∣ q₀₁ ≡ ∣fiber←[q₀₀=q₀₁]∣ q₀₁
    ∣fiber←[q₀₀=q₀₁=q₁₁]∣ i r p = ∣ fiber←[q₀₀=q₀₁=q₁₁] i r p ∣ₕ

  {- Definitions of fiber→← -}

  module _
    {x₁ : X}{y₀ : Y}(q₁₀ : Q x₁ y₀) where

    {- (x₀ , q₀₀) = (x₁ , q₁₀) -}
    module _
      {y₁ : Y}(q₁₁ : Q x₁ y₁)
      (r : inl x₁ ≡ inr y₁)
      (p : fiberSquarePush q₁₀ q₁₀ q₁₁ r) where

      fiber→←[q₀₀=q₁₀]-filler : (i j k l : I) → PushoutQ
      fiber→←[q₀₀=q₁₀]-filler i j k l' =
        let p' = fiber→[q₀₀=q₁₀] q₁₀ q₁₁ r p .snd in
        hfill (λ l → λ { (i = i0) → fiber←[q₁₁=q₀₁]-filler q₁₁ q₁₀ r p' j k l
                       ; (i = i1) → fiber→[q₀₀=q₁₀]-filler q₁₀ q₁₁ r p l k j
                       ; (j = i0) → push q₁₀ (~ k ∧ l)
                       ; (j = i1) → p' l k
                       ; (k = i0) → push q₁₀ (~ j ∧ l)
                       ; (k = i1) → push q₁₁ j })
              (inS (push q₁₁ (j ∧ k))) l'

      fiber→←[q₀₀=q₁₀] : fiber←[q₁₁=q₀₁] q₁₁ q₁₀ r (fiber→[q₀₀=q₁₀] q₁₀ q₁₁ r p .snd) .snd ≡ p
      fiber→←[q₀₀=q₁₀] i j k = fiber→←[q₀₀=q₁₀]-filler i j k i1

    {- (y₁ , q₁₁) = (y₀ , q₁₀) -}
    module _
      {x₀ : X}(q₀₀ : Q x₀ y₀)
      (r : inl x₀ ≡ inr y₀)
      (p : fiberSquarePush q₀₀ q₁₀ q₁₀ r) where

      fiber→←[q₁₁=q₁₀]-filler : (i j k l : I) → PushoutQ
      fiber→←[q₁₁=q₁₀]-filler i j k l' =
        let p' = fiber→[q₁₁=q₁₀] q₁₀ q₀₀ r p .snd in
        hfill (λ l → λ { (i = i0) → fiber←[q₀₀=q₀₁]-filler q₀₀ q₁₀ r p' j k l
                       ; (i = i1) → fiber→[q₁₁=q₁₀]-filler q₁₀ q₀₀ r p l k j
                       ; (j = i0) → push q₁₀ (~ k ∨ ~ l)
                       ; (j = i1) → p' l k
                       ; (k = i0) → push q₀₀ (~ j)
                       ; (k = i1) → push q₁₀ (j ∨ ~ l) })
              (inS (push q₀₀ (~ j ∨ k))) l'

      fiber→←[q₁₁=q₁₀] : fiber←[q₀₀=q₀₁] q₀₀ q₁₀ r (fiber→[q₁₁=q₁₀] q₁₀ q₀₀ r p .snd) .snd ≡ p
      fiber→←[q₁₁=q₁₀] i j k = fiber→←[q₁₁=q₁₀]-filler i j k i1

    {- q₀₀ = q₁₀ = q₁₁ -}
    fiber→←hypercube :
        (r : inl x₁ ≡ inr y₀)
      → (p : fiberSquarePush q₁₀ q₁₀ q₁₀ r)
      → PathP (λ i → fiber←[q₀₀=q₀₁=q₁₁] q₁₀ i r (fiber→[q₀₀=q₁₀=q₁₁] q₁₀ i r p .snd) .snd ≡ p)
              (fiber→←[q₀₀=q₁₀] q₁₀ r p) (fiber→←[q₁₁=q₁₀] q₁₀ r p)
    fiber→←hypercube r p i j u v =
      hcomp (λ l → λ { (i = i0) → fiber→←[q₀₀=q₁₀]-filler q₁₀ r p j u v l
                     ; (i = i1) → fiber→←[q₁₁=q₁₀]-filler q₁₀ r p j u v l
                     ; (j = i0) → fiber←[q₀₀=q₀₁=q₁₁]-filler q₁₀ r (fiber→[q₀₀=q₁₀=q₁₁] q₁₀ i r p .snd) i u v l
                     ; (j = i1) → fiber→[q₀₀=q₁₀=q₁₁]-filler q₁₀ r p i l v u
                     ; (u = i0) → push q₁₀ ((i ∨ (~ v ∧ l)) ∧ (~ v ∨ (i ∧ ~ l)))
                     ; (u = i1) → fiber→[q₀₀=q₁₀=q₁₁] q₁₀ i r p .snd l v
                     ; (v = i0) → push q₁₀ ((i ∨ l) ∧ ~ u)
                     ; (v = i1) → push q₁₀ ((i ∧ ~ l) ∨ u) })
            (push q₁₀ ((i ∨ (v ∧ u)) ∧ (v ∨ (i ∧ ~ u))))

  {- Definitions of fiber←→ -}

  module _
    {x₀ : X}{y₁ : Y}(q₀₁ : Q x₀ y₁) where

    {- (x₁ , q₁₁) = (x₀ , q₀₁) -}
    module _
      {y₀ : Y}(q₀₀ : Q x₀ y₀)
      (r : inl x₀ ≡ inr y₁)
      (p : push q₀₁ ≡ r) where

      fiber←→[q₁₁=q₀₁]-filler : (i j k l : I) → PushoutQ
      fiber←→[q₁₁=q₀₁]-filler i j k l' =
        let p' = fiber←[q₁₁=q₀₁] q₀₁ q₀₀ r p .snd in
        hfill (λ l → λ { (i = i0) → fiber→[q₀₀=q₁₀]-filler q₀₀ q₀₁ r p' j k l
                       ; (i = i1) → fiber←[q₁₁=q₀₁]-filler q₀₁ q₀₀ r p l k j
                       ; (j = i0) → push q₀₁ (k ∧ l)
                       ; (j = i1) → p' l k
                       ; (k = i0) → push q₀₀ (j ∧ ~ l)
                       ; (k = i1) → push q₀₁ l })
              (inS (push q₀₀ (j ∧ ~ k))) l'

      fiber←→[q₁₁=q₀₁] : fiber→[q₀₀=q₁₀] q₀₀ q₀₁ r (fiber←[q₁₁=q₀₁] q₀₁ q₀₀ r p .snd) .snd ≡ p
      fiber←→[q₁₁=q₀₁] i j k = fiber←→[q₁₁=q₀₁]-filler i j k i1

    {- (y₀ , q₀₀) = (y₁ , q₀₁) -}
    module _
      {x₁ : X}(q₁₁ : Q x₁ y₁)
      (r : inl x₀ ≡ inr y₁)
      (p : push q₀₁ ≡ r) where

      fiber←→[q₀₀=q₀₁]-filler : (i j k l : I) → PushoutQ
      fiber←→[q₀₀=q₀₁]-filler i j k l' =
        let p' = fiber←[q₀₀=q₀₁] q₀₁ q₁₁ r p .snd in
        hfill (λ l → λ { (i = i0) → fiber→[q₁₁=q₁₀]-filler q₁₁ q₀₁ r p' j k l
                       ; (i = i1) → fiber←[q₀₀=q₀₁]-filler q₀₁ q₁₁ r p l k j
                       ; (j = i0) → push q₀₁ (k ∨ ~ l)
                       ; (j = i1) → p' l k
                       ; (k = i0) → push q₀₁ (~ l)
                       ; (k = i1) → push q₁₁ (~ j ∨ l) })
              (inS (push q₁₁ (~ j ∨ ~ k))) l'

      fiber←→[q₀₀=q₀₁] : fiber→[q₁₁=q₁₀] q₁₁ q₀₁ r (fiber←[q₀₀=q₀₁] q₀₁ q₁₁ r p .snd) .snd ≡ p
      fiber←→[q₀₀=q₀₁] i j k = fiber←→[q₀₀=q₀₁]-filler i j k i1

    {- q₀₀ = q₀₁ = q₁₁ -}
    fiber←→hypercube :
        (r : inl x₀ ≡ inr y₁)
      → (p : push q₀₁ ≡ r)
      → PathP (λ i → fiber→[q₀₀=q₁₀=q₁₁] q₀₁ i r (fiber←[q₀₀=q₀₁=q₁₁] q₀₁ i r p .snd) .snd ≡ p)
              (fiber←→[q₁₁=q₀₁] q₀₁ r p) (fiber←→[q₀₀=q₀₁] q₀₁ r p)
    fiber←→hypercube r p i j u v =
      hcomp (λ l → λ { (i = i0) → fiber←→[q₁₁=q₀₁]-filler q₀₁ r p j u v l
                     ; (i = i1) → fiber←→[q₀₀=q₀₁]-filler q₀₁ r p j u v l
                     ; (j = i0) → fiber→[q₀₀=q₁₀=q₁₁]-filler q₀₁ r (fiber←[q₀₀=q₀₁=q₁₁] q₀₁ i r p .snd) i u v l
                     ; (j = i1) → fiber←[q₀₀=q₀₁=q₁₁]-filler q₀₁ r p i l v u
                     ; (u = i0) → push q₀₁ ((i ∨ (v ∧ l)) ∧ (v ∨ (i ∧ ~ l)))
                     ; (u = i1) → fiber←[q₀₀=q₀₁=q₁₁] q₀₁ i r p .snd l v
                     ; (v = i0) → push q₀₁ ((i ∨ u) ∧ ~ l)
                     ; (v = i1) → push q₀₁ ((i ∧ ~ u) ∨ l) })
           (push q₀₁ ((i ∨ (~ v ∧ u)) ∧ (~ v ∨ (i ∧ ~ u))))

  module Fiber→
    {x₁ : X}{y₀ : Y}(q₁₀ : Q x₁ y₀) =
    WedgeConnectivity m n
      (leftFiber  x₁ , (y₀ , q₁₀)) (leftConn  x₁)
      (rightFiber y₀ , (x₁ , q₁₀)) (rightConn y₀)
      (λ (y₁ , q₁₁) (x₀ , q₀₀) →
        (((r : inl x₀ ≡ inr y₁) → fiberSquarePush q₀₀ q₁₀ q₁₁ r → rightCode _ r)
        , isOfHLevelΠ2 _ (λ x y → isOfHLevelTrunc _)))
      (λ (y₁ , q₁₁) → ∣fiber→[q₀₀=q₁₀]∣ q₁₀ q₁₁)
      (λ (x₀ , q₀₀) → ∣fiber→[q₁₁=q₁₀]∣ q₁₀ q₀₀)
      (∣fiber→[q₀₀=q₁₀=q₁₁]∣ q₁₀)

  fiber→ :
      {x₁ : X}{y₀ : Y}(q₁₀ : Q x₁ y₀)
    → {x₀ : X}(q₀₀ : Q x₀ y₀) → {y₁ : Y}(q₁₁ : Q x₁ y₁)
    → (r : inl x₀ ≡ inr y₁)
    → fiberSquarePush q₀₀ q₁₀ q₁₁ r → rightCode _ r
  fiber→ q₁₀ q₀₀ q₁₁ = Fiber→.extension q₁₀ (_ , q₁₁) (_ , q₀₀)

  module Fiber←
    {x₀ : X}{y₁ : Y}(q₀₁ : Q x₀ y₁) =
    WedgeConnectivity m n
      (leftFiber  x₀ , (y₁ , q₀₁)) (leftConn  x₀)
      (rightFiber y₁ , (x₀ , q₀₁)) (rightConn y₁)
      (λ (y₀ , q₀₀) (x₁ , q₁₁) →
        (((r : inl x₀ ≡ inr y₁) → push q₀₁ ≡ r → leftCodeExtended q₀₀ _ (push q₁₁) r)
        , isOfHLevelΠ2 _ (λ x y → isOfHLevelTrunc _)))
      (λ (y₀ , q₀₀) → ∣fiber←[q₁₁=q₀₁]∣ q₀₁ q₀₀)
      (λ (x₁ , q₁₁) → ∣fiber←[q₀₀=q₀₁]∣ q₀₁ q₁₁)
      (∣fiber←[q₀₀=q₀₁=q₁₁]∣ q₀₁)

  fiber← :
      {x₀ : X}{y₁ : Y}(q₀₁ : Q x₀ y₁)
    → {y₀ : Y}(q₀₀ : Q x₀ y₀) → {x₁ : X}(q₁₁ : Q x₁ y₁)
    → (r : inl x₀ ≡ inr y₁)
    → push q₀₁ ≡ r → leftCodeExtended q₀₀ _ (push q₁₁) r
  fiber← q₀₁ q₀₀ q₁₁ = Fiber←.extension q₀₁ (_ , q₀₀) (_ , q₁₁)

  module _
    {x₀ x₁ : X}{y₀ y₁ : Y}
    (q₀₀ : Q x₀ y₀)(q₁₁ : Q x₁ y₁)
    (r : inl x₀ ≡ inr y₁) where

    left→rightCodeExtended : leftCodeExtended q₀₀ _ (push q₁₁) r → rightCode _ r
    left→rightCodeExtended =
      rec (isOfHLevelTrunc _) (λ (q₁₀ , p) → fiber→ q₁₀ q₀₀ q₁₁ r p)

    right→leftCodeExtended : rightCode _ r → leftCodeExtended q₀₀ _ (push q₁₁) r
    right→leftCodeExtended =
      rec (isOfHLevelTrunc _) (λ (q₀₁ , p) → fiber← q₀₁ q₀₀ q₁₁ r p)

  {- Definition of one-side homotopy -}

  module _
    {x₁ : X}{y₀ : Y}(q₁₀ : Q x₁ y₀) where

    {- (x₀ , q₀₀) = (x₁ , q₁₀) -}
    module _
      {y₁ : Y}(q₁₁ : Q x₁ y₁)
      (r : inl x₁ ≡ inr y₁)
      (p : fiberSquarePush q₁₀ q₁₀ q₁₁ r) where

      ∣fiber→←[q₀₀=q₁₀]∣ : right→leftCodeExtended q₁₀ q₁₁ r (fiber→ q₁₀ q₁₀ q₁₁ r p) ≡ ∣ q₁₀ , p ∣ₕ
      ∣fiber→←[q₀₀=q₁₀]∣ =
          (λ i → right→leftCodeExtended q₁₀ q₁₁ r (Fiber→.left q₁₀ (_ , q₁₁) i r p))
        ∙ recUniq {n = m + n} _ _ _
        ∙ (λ i → Fiber←.left q₁₁ (_ , q₁₀) i r (fiber→[q₀₀=q₁₀] q₁₀ q₁₁ r p .snd))
        ∙ (λ i → ∣ q₁₀ , fiber→←[q₀₀=q₁₀] q₁₀ q₁₁ r p i ∣ₕ)

    {- (y₁ , q₁₁) = (y₀ , q₁₀) -}
    module _
      {x₀ : X}(q₀₀ : Q x₀ y₀)
      (r : inl x₀ ≡ inr y₀)
      (p : fiberSquarePush q₀₀ q₁₀ q₁₀ r) where

      ∣fiber→←[q₁₁=q₁₀]∣ : right→leftCodeExtended q₀₀ q₁₀ r (fiber→ q₁₀ q₀₀ q₁₀ r p) ≡ ∣ q₁₀ , p ∣ₕ
      ∣fiber→←[q₁₁=q₁₀]∣ =
          (λ i → right→leftCodeExtended q₀₀ q₁₀ r (Fiber→.right q₁₀ (_ , q₀₀) i r p))
        ∙ recUniq {n = m + n} _ _ _
        ∙ (λ i → Fiber←.right q₀₀ (_ , q₁₀) i r (fiber→[q₁₁=q₁₀] q₁₀ q₀₀ r p .snd))
        ∙ (λ i → ∣ q₁₀ , fiber→←[q₁₁=q₁₀] q₁₀ q₀₀ r p i ∣ₕ)

    {- q₀₀ = q₁₁ = q₁₀ -}
    module _
      (r : inl x₁ ≡ inr y₀)
      (p : fiberSquarePush q₁₀ q₁₀ q₁₀ r) where

      path→←Square =
           (λ i j → right→leftCodeExtended q₁₀ q₁₀ r (Fiber→.homSquare q₁₀ i j r p))
        ∙₂ (λ i → recUniq {n = m + n} _ _ _)
        ∙₂ (λ i j → Fiber←.homSquare q₁₀ i j r (fiber→[q₀₀=q₁₀=q₁₁] q₁₀ i r p .snd))
        ∙₂ (λ i j → ∣ (q₁₀ , fiber→←hypercube q₁₀ r p i j) ∣ₕ)

    ∣fiber→←[q₀₀=q₁₀=q₁₁]∣ : ∣fiber→←[q₀₀=q₁₀]∣ q₁₀ ≡ ∣fiber→←[q₁₁=q₁₀]∣ q₁₀
    ∣fiber→←[q₀₀=q₁₀=q₁₁]∣ i r p = path→←Square r p i

  fiber→← :
      {x₁ : X}{y₀ : Y}(q₁₀ : Q x₁ y₀)
    → {x₀ : X}(q₀₀ : Q x₀ y₀) → {y₁ : Y}(q₁₁ : Q x₁ y₁)
    → (r : inl x₀ ≡ inr y₁)
    → (p : fiberSquarePush q₀₀ q₁₀ q₁₁ r)
    → right→leftCodeExtended q₀₀ q₁₁ r (fiber→ q₁₀ q₀₀ q₁₁ r p) ≡ ∣ q₁₀ , p ∣ₕ
  fiber→← {x₁ = x₁} {y₀ = y₀} q₁₀ q₀₀' q₁₁' =
    WedgeConnectivity.extension m n
      (leftFiber  x₁ , (y₀ , q₁₀)) (leftConn  x₁)
      (rightFiber y₀ , (x₁ , q₁₀)) (rightConn y₀)
      (λ (y₁ , q₁₁) (x₀ , q₀₀) →
        ((  (r : inl x₀ ≡ inr y₁) → (p : fiberSquarePush q₀₀ q₁₀ q₁₁ r)
          → right→leftCodeExtended q₀₀ q₁₁ r (fiber→ q₁₀ q₀₀ q₁₁ r p) ≡ ∣ q₁₀ , p ∣ₕ )
        , isOfHLevelΠ2 _ (λ x y → isOfHLevelTruncPath)))
      (λ (y₁ , q₁₁) → ∣fiber→←[q₀₀=q₁₀]∣ q₁₀ q₁₁)
      (λ (x₀ , q₀₀) → ∣fiber→←[q₁₁=q₁₀]∣ q₁₀ q₀₀)
      (∣fiber→←[q₀₀=q₁₀=q₁₁]∣ q₁₀)
      (_ , q₁₁') (_ , q₀₀')

  {- Definition of the other side homotopy -}

  module _
    {x₀ : X}{y₁ : Y}(q₀₁ : Q x₀ y₁) where

    {- (x₁ , q₁₁) = (x₀ , q₀₁) -}
    module _
      {y₀ : Y}(q₀₀ : Q x₀ y₀)
      (r : inl x₀ ≡ inr y₁)
      (p : push q₀₁ ≡ r) where

      ∣fiber←→[q₁₁=q₀₁]∣ : left→rightCodeExtended q₀₀ q₀₁ r (fiber← q₀₁ q₀₀ q₀₁ r p) ≡ ∣ q₀₁ , p ∣ₕ
      ∣fiber←→[q₁₁=q₀₁]∣ =
          (λ i → left→rightCodeExtended q₀₀ q₀₁ r (Fiber←.left q₀₁ (_ , q₀₀) i r p))
        ∙ recUniq {n = m + n} _ _ _
        ∙ (λ i → Fiber→.left q₀₀ (_ , q₀₁) i r (fiber←[q₁₁=q₀₁] q₀₁ q₀₀ r p .snd))
        ∙ (λ i → ∣ q₀₁ , fiber←→[q₁₁=q₀₁] q₀₁ q₀₀ r p i ∣ₕ)

    {- (y₀ , q₀₀) = (y₁ , q₀₁) -}
    module _
      {x₁ : X}(q₁₁ : Q x₁ y₁)
      (r : inl x₀ ≡ inr y₁)
      (p : push q₀₁ ≡ r) where

      ∣fiber←→[q₀₀=q₀₁]∣ : left→rightCodeExtended q₀₁ q₁₁ r (fiber← q₀₁ q₀₁ q₁₁ r p) ≡ ∣ q₀₁ , p ∣ₕ
      ∣fiber←→[q₀₀=q₀₁]∣  =
          (λ i → left→rightCodeExtended q₀₁ q₁₁ r (Fiber←.right q₀₁ (_ , q₁₁) i r p))
        ∙ recUniq {n = m + n} _ _ _
        ∙ (λ i → Fiber→.right q₁₁ (_ , q₀₁) i r (fiber←[q₀₀=q₀₁] q₀₁ q₁₁ r p .snd))
        ∙ (λ i → ∣ q₀₁ , fiber←→[q₀₀=q₀₁] q₀₁ q₁₁ r p i ∣ₕ)

    {- q₀₀ = q₀₁ = q₁₁ -}
    module _
      (r : inl x₀ ≡ inr y₁)
      (p : push q₀₁ ≡ r) where

      path←→Square =
           (λ i j → left→rightCodeExtended q₀₁ q₀₁ r (Fiber←.homSquare q₀₁ i j r p))
        ∙₂ (λ i → recUniq {n = m + n} _ _ _)
        ∙₂ (λ i j → Fiber→.homSquare q₀₁ i j r (fiber←[q₀₀=q₀₁=q₁₁] q₀₁ i r p .snd))
        ∙₂ (λ i j → ∣ q₀₁ , fiber←→hypercube q₀₁ r p i j ∣ₕ)

    ∣fiber←→[q₀₀=q₀₁=q₁₁]∣ : ∣fiber←→[q₁₁=q₀₁]∣ q₀₁ ≡ ∣fiber←→[q₀₀=q₀₁]∣ q₀₁
    ∣fiber←→[q₀₀=q₀₁=q₁₁]∣ i r p = path←→Square r p i

  fiber←→ :
      {x₀ : X}{y₁ : Y}(q₀₁ : Q x₀ y₁)
    → {y₀ : Y}(q₀₀ : Q x₀ y₀) → {x₁ : X}(q₁₁ : Q x₁ y₁)
    → (r : inl x₀ ≡ inr y₁)
    → (p : push q₀₁ ≡ r)
    → left→rightCodeExtended q₀₀ q₁₁ r (fiber← q₀₁ q₀₀ q₁₁ r p) ≡ ∣ q₀₁ , p ∣ₕ
  fiber←→ {x₀ = x₀} {y₁ = y₁} q₀₁ q₀₀' q₁₁' =
    WedgeConnectivity.extension m n
      (leftFiber  x₀ , (y₁ , q₀₁)) (leftConn  x₀)
      (rightFiber y₁ , (x₀ , q₀₁)) (rightConn y₁)
      (λ (y₀ , q₀₀) (x₁ , q₁₁) →
        ((  (r : inl x₀ ≡ inr y₁) → (p : push q₀₁ ≡ r)
          → left→rightCodeExtended q₀₀ q₁₁ r (fiber← q₀₁ q₀₀ q₁₁ r p) ≡ ∣ q₀₁ , p ∣ₕ )
        , isOfHLevelΠ2 _ (λ x y → isOfHLevelTruncPath)))
      (λ (y₀ , q₀₀) → ∣fiber←→[q₁₁=q₀₁]∣ q₀₁ q₀₀)
      (λ (x₁ , q₁₁) → ∣fiber←→[q₀₀=q₀₁]∣ q₀₁ q₁₁)
      (∣fiber←→[q₀₀=q₀₁=q₁₁]∣ q₀₁)
      (_ , q₀₀') (_ , q₁₁')

  module _
    {x₀ x₁ : X}{y₀ y₁ : Y}
    (q₀₀ : Q x₀ y₀)(q₁₁ : Q x₁ y₁)
    (r : inl x₀ ≡ inr y₁) where

    left→right→leftCodeExtended :
        (a : leftCodeExtended q₀₀ _ (push q₁₁) r)
      → right→leftCodeExtended q₀₀ q₁₁ r (left→rightCodeExtended q₀₀ q₁₁ r a) ≡ a
    left→right→leftCodeExtended a =
      sym (∘rec _ _ _ (right→leftCodeExtended q₀₀ q₁₁ r) a) ∙
      (λ i → recId _ (λ (q₁₀ , p) → fiber→← q₁₀ q₀₀ q₁₁ r p) i a)

    right→left→rightCodeExtended :
        (a : rightCode _ r)
      → left→rightCodeExtended q₀₀ q₁₁ r (right→leftCodeExtended q₀₀ q₁₁ r a) ≡ a
    right→left→rightCodeExtended a =
      sym (∘rec _ _ _ (left→rightCodeExtended q₀₀ q₁₁ r) a) ∙
      (λ i → recId _ (λ (q₀₁ , p) → fiber←→ q₀₁ q₀₀ q₁₁ r p) i a)

    left≃rightCodeExtended : leftCodeExtended q₀₀ _ (push q₁₁) r ≃ rightCode y₁ r
    left≃rightCodeExtended =
      isoToEquiv (iso (left→rightCodeExtended _ _ _) (right→leftCodeExtended _ _ _)
                       right→left→rightCodeExtended left→right→leftCodeExtended)

  {- Definition and properties of Code -}

  module _ (x₀ : X)(y₀ : Y)(q₀₀ : Q x₀ y₀) where

    leftCode' : (x : X){p : PushoutQ} → inl x ≡ p → inl x₀ ≡ p → Type ℓ
    leftCode' x r' = leftCodeExtended q₀₀ x r'

    leftCode : (x : X) → inl x₀ ≡ inl x → Type ℓ
    leftCode x = leftCode' x refl

    fiberPath : {x : X}{y : Y} → (q : Q x y) → leftCode' x (push q) ≡ rightCode y
    fiberPath q i r = ua (left≃rightCodeExtended q₀₀ q r) i

    pushCode :
        {x : X}{y : Y} → (q : Q x y)
      → PathP (λ i → inl x₀ ≡ push q i → Type ℓ) (leftCode x) (rightCode y)
    pushCode q i =
      hcomp (λ j → λ { (i = i0) → leftCode _
                     ; (i = i1) → fiberPath q j })
            (leftCode' _ (λ j → push q (i ∧ j)))

    Code : (p : PushoutQ) → inl x₀ ≡ p → Type ℓ
    Code (inl x) = leftCode  x
    Code (inr y) = rightCode y
    Code (push q i) = pushCode q i

    {- Transportation rule of pushCode -}

    transpLeftCode : (y : Y) → (q : Q x₀ y) → (q' : leftCodeExtended q₀₀ _ refl refl) → leftCode' _ (push q) (push q)
    transpLeftCode y q q' =
      transport (λ i → leftCode' _ (λ j → push q (i ∧ j)) (λ j → push q (i ∧ j))) q'

    transpPushCodeβ' :
        (y : Y) → (q : Q x₀ y) → (q' : leftCodeExtended q₀₀ _ refl refl)
      → transport (λ i → pushCode q i (λ j → push q (i ∧ j))) q' ≡ left→rightCodeExtended _ _ _ (transpLeftCode y q q')
    transpPushCodeβ' y q q' i = transportRefl (left→rightCodeExtended _ _ _ (transpLeftCode y q (transportRefl q' i))) i

    module _
      {p : PushoutQ}(r : inl x₀ ≡ p) where

      fiber-filler : I → Type ℓ
      fiber-filler i = fiber' q₀₀ (λ j → r (i ∧ j)) (λ j → r (i ∧ j))

      module _
        (q : fiberSquare q₀₀ q₀₀ refl refl) where

        transpLeftCode-filler : (i j k : I) → PushoutQ
        transpLeftCode-filler i j k' =
          hfill (λ k → λ { (i = i0) → push q₀₀ (~ j)
                         ; (i = i1) → r (j ∧ k)
                         ; (j = i0) → push q₀₀ (~ i)
                         ; (j = i1) → r (i ∧ k) })
                (inS (q i j)) k'

    transpLeftCodeβ' :
        {p : PushoutQ} → (r : inl x₀ ≡ p) → (q : fiberSquare q₀₀ q₀₀ refl refl)
      → transport (λ i → fiber-filler r i) (q₀₀ , q) ≡ (q₀₀ , λ i j → transpLeftCode-filler r q i j i1)
    transpLeftCodeβ' r q =
      J (λ p r → transport (λ i → fiber-filler r i) (q₀₀ , q) ≡ (q₀₀ , λ i j → transpLeftCode-filler r q i j i1))
        (transportRefl _ ∙ (λ k → (q₀₀ , λ i j → transpLeftCode-filler refl q i j k))) r

    transpLeftCodeβ :
        (y : Y) → (q : Q x₀ y) → (q' : fiberSquare q₀₀ q₀₀ refl refl)
      → transpLeftCode y q ∣ q₀₀ , q' ∣ₕ ≡ ∣ q₀₀ , (λ i j → transpLeftCode-filler (push q) q' i j i1) ∣ₕ
    transpLeftCodeβ y q q' = transportTrunc _ ∙ (λ i → ∣ transpLeftCodeβ' _ q' i ∣ₕ)

    transpPushCodeβ :
        (y : Y) → (q : Q x₀ y) → (q' : fiberSquare q₀₀ q₀₀ refl refl)
      →   transport (λ i → pushCode q i (λ j → push q (i ∧ j))) ∣ q₀₀ , q' ∣ₕ
        ≡ ∣fiber→[q₀₀=q₁₀]∣ q₀₀ q (push q) (λ i j → transpLeftCode-filler (push q) q' i j i1)
    transpPushCodeβ y q q' =
        transpPushCodeβ' _ _ _
      ∙ (λ i → left→rightCodeExtended _ _ _ (transpLeftCodeβ _ _ q' i))
      ∙ recUniq {n = m + n} _ _ _
      ∙ (λ i' → Fiber→.left q₀₀ (_ , q) i' (push q) (λ i j → transpLeftCode-filler (push q) q' i j i1))

    {- The contractibility of Code -}

    centerCode : {p : PushoutQ} → (r : inl x₀ ≡ p) → Code p r
    centerCode r =
      transport (λ i → Code _ (λ j → r (i ∧ j))) ∣ q₀₀ , (λ i j → push q₀₀ (~ i ∧ ~ j)) ∣ₕ

    module _
      (y : Y)(q : Q x₀ y) where

      transp-filler : (i j k : I) → PushoutQ
      transp-filler = transpLeftCode-filler (push q) (λ i' j' → push q₀₀ (~ i' ∧ ~ j'))

      transp-square : fiberSquare q₀₀ q₀₀ (push q) (push q)
      transp-square i j = transp-filler i j i1

      contractionCodeRefl' :
        fiber→[q₀₀=q₁₀] q₀₀ q (push q) transp-square .snd ≡ refl
      contractionCodeRefl' i j k =
        hcomp (λ l → λ { (i = i0) → fiber→[q₀₀=q₁₀]-filler q₀₀ q (push q) transp-square j k l
                       ; (i = i1) → transp-square (~ j ∨ l) k
                       ; (j = i0) → push q (k ∧ (i ∨ l))
                       ; (j = i1) → transp-square l k
                       ; (k = i0) → push q₀₀ (j ∧ ~ l)
                       ; (k = i1) → push q ((i ∧ ~ j) ∨ l) })
              (transp-filler (~ j) k i)

      contractionCodeRefl : centerCode (push q) ≡ ∣ q , refl ∣ₕ
      contractionCodeRefl = transpPushCodeβ _ _ _ ∙ (λ i → ∣ q , contractionCodeRefl' i ∣ₕ)

    module _
      (y : Y)(r : inl x₀ ≡ inr y) where

      contractionCode' : (a : fiber push r) → centerCode r ≡ ∣ a ∣ₕ
      contractionCode' (q , p') = J (λ r' p → centerCode r' ≡ ∣ q , p ∣ₕ) (contractionCodeRefl _ q) p'

      contractionCode : (a : Code _ r) → centerCode r ≡ a
      contractionCode = elim (λ _ → isOfHLevelTruncPath) contractionCode'

      isContrCode : isContr (Code _ r)
      isContrCode = centerCode r , contractionCode

  excision-helper :
      (x : X) → Trunc (1 + m) (Σ[ y₀ ∈ Y ] Q x y₀)
    → (y : Y) → (r : inl x ≡ inr y) → isContr (Trunc (m + n) (fiber push r))
  excision-helper x y' y r = rec (isProp→isOfHLevelSuc m isPropIsContr) (λ (y₀ , q₀₀) → isContrCode x y₀ q₀₀ y r ) y'

  {- The Main Result : Blakers-Massey Homotopy Excision Theorem -}
  Excision : (x : X)(y : Y) → isConnectedFun (m + n) (push {x = x} {y = y})
  Excision x y = excision-helper x (leftConn x .fst) y


{-
We also give the following version of the theorem: Given a square

          g
  A --------------> C
  |\              ↗ |
  |  \         ↗    |
  |    \    ↗       |
f |      X          |  inr
  |    /            |
  |   /             |
  |  /              |
  v /               v
  B -----------> Pushout f g
         inl

where X is the pullback of inl and inr
  (X := Σ[ (b , c) ∈ B × C ] (inl b ≡ inr c)).

If f in n-connected and g in m-connected, then the diagonal map
A → X is (n+m)-connected
-}


private
  shuffleFibIso₁ :
       {ℓ ℓ' ℓ'' : Level} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
       (f : A → B) (g : A → C) (b : B)
     → Iso (Σ[ c ∈ C ] Σ[ a ∈ A ] (f a ≡ b) × (g a ≡ c))
             (Σ[ a ∈ A ] ((Σ[ c ∈ C ] (g a ≡ c)) × (f a ≡ b)))
  shuffleFibIso₁ f g b =
    compIso (invIso Σ-assoc-Iso)
     (compIso (Σ-cong-iso-fst Σ-swap-Iso)
      (compIso
       (Σ-cong-iso-snd (λ y → Σ-swap-Iso))
       (compIso Σ-assoc-Iso
         (Σ-cong-iso-snd λ a → invIso Σ-assoc-Iso))))

  shuffleFibIso₂ : {ℓ ℓ' ℓ'' : Level} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
         (f : A → B) (g : A → C) (x : _)
         → Iso (Σ[ a ∈ A ] ((Σ[ c ∈ C ] (g a ≡ c)) × (f a ≡ x)))
                (fiber f x)
  shuffleFibIso₂ f g x = Σ-cong-iso-snd
        λ a → compIso (Σ-cong-iso-fst
                        (isContr→Iso (isContrSingl (g a))
                         isContrUnit))
                       lUnit×Iso

module BlakersMassey□ {ℓ ℓ' ℓ'' : Level}
  {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
  (f : A → B) (g : A → C) (n m : ℕ)
  (con-f : isConnectedFun (suc n) f)
  (con-g : isConnectedFun (suc m) g) where

  {- Some abbreviations and connectivity -}
  private
    fib = doubleFib f g

    B-con : (x : B) → isConnected (suc n) (Σ[ c ∈ C ] (fib x c))
    B-con x =
      isConnectedRetractFromIso (suc n)
        (compIso
          (shuffleFibIso₁ f g x)
          (shuffleFibIso₂ f g x))
        (con-f x)

    C-con : (c : C) → isConnected (suc m) (Σ[ b ∈ B ] (fib b c))
    C-con c =
      isConnectedRetractFromIso (suc m)
        (compIso
          (compIso (Σ-cong-iso-snd
                    (λ _ → Σ-cong-iso-snd λ _ → Σ-swap-Iso))
            (shuffleFibIso₁ g f c))
            (shuffleFibIso₂ g f c))
        (con-g c)

  open module BM-f-g = BlakersMassey B C fib {m = n} B-con {n = m} C-con

  fib× : (B × C) → Type _
  fib× (b , c) = fib b c

  PushoutGenPath× : B × C → Type _
  PushoutGenPath× (b , c) = Path (PushoutGen fib) (inl b) (inr c)

  PushoutPath× : B × C → Type _
  PushoutPath× (b , c) = Path (Pushout f g) (inl b) (inr c)

  {- The function in question -}
  toPullback : A → Σ (B × C) PushoutPath×
  toPullback a = (f a , g a) , push a

  {- We redescribe toPullback as a composition of three maps,
     two of which are equivs and one of which is (n+m)-connected -}
  Totalfib×→Total : Σ (B × C) fib× → Σ (B × C) PushoutGenPath×
  Totalfib×→Total =
    TotalFun {A = B × C} {B = fib×} {C = PushoutGenPath×} (λ a → push)

  isConnectedTotalFun : isConnectedFun (n + m) Totalfib×→Total
  isConnectedTotalFun =
    FunConnected→TotalFunConnected (λ _ → push) (n + m) (uncurry BM-f-g.Excision)

  TotalPathGen×Iso : Iso (Σ (B × C) PushoutGenPath×) (Σ (B × C) PushoutPath×)
  TotalPathGen×Iso =
    Σ-cong-iso-snd λ x
      → congIso (invIso (IsoPushoutPushoutGen f g))

  Totalfib×Iso : Iso (Σ (B × C) fib×) A
  fun Totalfib×Iso ((b , c) , a , p) = a
  inv Totalfib×Iso a = (f a , g a) , a , refl , refl
  rightInv Totalfib×Iso _ = refl
  leftInv Totalfib×Iso ((b , c) , a , (p , q)) i =
    ((p i) , (q i)) , (a , ((λ j → p (i ∧ j)) , (λ j → q (i ∧ j))))

  toPullback' : A → Σ (B × C) PushoutPath×
  toPullback' =
    (fun TotalPathGen×Iso ∘ Totalfib×→Total) ∘ inv Totalfib×Iso

  toPullback'≡toPullback : toPullback' ≡ toPullback
  toPullback'≡toPullback =
    funExt λ x → ΣPathP (refl , (sym (rUnit (push x))))

  isConnected-toPullback : isConnectedFun (n + m) toPullback
  isConnected-toPullback =
    subst (isConnectedFun (n + m)) toPullback'≡toPullback
      (isConnectedComp
        (fun TotalPathGen×Iso ∘ Totalfib×→Total)
        (inv Totalfib×Iso) (n + m)
        (isConnectedComp (fun TotalPathGen×Iso) Totalfib×→Total (n + m)
          (isEquiv→isConnected _ (isoToIsEquiv TotalPathGen×Iso) (n + m))
          isConnectedTotalFun)
        (isEquiv→isConnected _ (isoToIsEquiv (invIso Totalfib×Iso)) (n + m)))

-- Consequence of Blakers-Massey: connectedness of ⋁↪ (wedge inclusion)
isConnected⋁↪ : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} {n m : ℕ}
  → isConnected (suc (suc n)) (fst A)
  → isConnected (suc (suc m)) (fst B)
  → isConnectedFun (suc m + suc n) (⋁↪ {A = A} {B})
isConnected⋁↪ {A = A} {B} {n} {m} cA cB =
  subst (isConnectedFun (suc m + suc n)) (sym main)
    (isConnectedComp _  _ _
      (isEquiv→isConnected _ (isoToIsEquiv lem) _)
      isConnected-toPullback)
  where
  isConnectedFoldL : (cB : isConnected (suc (suc m)) (fst B))
    → isConnectedFun (suc (suc m)) proj⋁ₗ
  isConnectedFoldL cB = subst (isConnectedFun (suc (suc m)))
      (funExt (λ { (inl x) → refl
                 ; (inr x) → refl
                 ; (push a i) → refl}))
      conf
    where
    f' : A ⋁ B → fst A
    f' = Iso.fun cofibInr-⋁ ∘ inr

    conf : isConnectedFun (suc (suc m)) f'
    conf = isConnectedComp (Iso.fun cofibInr-⋁) inr
             (suc (suc m))
               (isEquiv→isConnected _ (isoToIsEquiv cofibInr-⋁) (suc (suc m)))
               (inrConnected (suc (suc m)) _ _
                 (isConnected→isConnectedFun (suc (suc m)) cB))

  isConnectedFoldR : (cA : isConnected (suc (suc n)) (fst A))
    → isConnectedFun (suc (suc n)) proj⋁ᵣ
  isConnectedFoldR cA =
    subst (isConnectedFun (suc (suc n)))
      (funExt (λ { (inl x) → refl ; (inr x) → refl ; (push a i) → refl}))
      conf
    where
    f' : A ⋁ B → fst B
    f' = (Iso.fun cofibInr-⋁ ∘ inr) ∘ fst (symPushout _ _)

    conf : isConnectedFun (suc (suc n)) f'
    conf =
      isConnectedComp (Iso.fun cofibInr-⋁ ∘ inr) (fst (symPushout _ _))
        (suc (suc n))
        (isConnectedComp _ inr (suc (suc n))
          (isEquiv→isConnected _ (isoToIsEquiv cofibInr-⋁) (suc (suc n)))
          (inrConnected (suc (suc n)) _ _
            (isConnected→isConnectedFun (suc (suc n)) cA)))
             (isEquiv→isConnected _ (snd (symPushout _ _)) (suc (suc n)))

  open BlakersMassey□ {A = A ⋁ B} {B = fst A} {C = fst B}
    proj⋁ₗ proj⋁ᵣ (suc m) (suc n)
      (isConnectedFoldL cB) (isConnectedFoldR cA)

  lem : Iso (Σ (fst A × fst B) PushoutPath×) (fst A × fst B)
  lem = compIso
         (Σ-cong-iso-snd (λ _ →
           equivToIso (isContr→≃Unit
             (isOfHLevelPath 0 (isContrPushout-proj⋁ A B) _ _))))
           rUnit×Iso

  main : ⋁↪ ≡ Iso.fun lem ∘ toPullback
  main = funExt λ { (inl x) → refl
                  ; (inr x) → refl
                  ; (push a i) → refl}

{-

Eilenberg–Mac Lane type K(G, 1)

-}

{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.HITs.EilenbergMacLane1.Properties where

open import Cubical.HITs.EilenbergMacLane1.Base

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.Algebra.Group.Base

open import Cubical.HITs.PropositionalTruncation as PropTrunc using (∥_∥; ∣_∣; squash)
open import Cubical.HITs.SetTruncation as SetTrunc using (∥_∥₂; ∣_∣₂; squash₂)

private
  variable
    ℓG ℓ : Level

module _ ((G , str) : Group {ℓG}) where

  open GroupStr str

  elimEq : {B : EM₁ (G , str) → Type ℓ}
           (Bprop : (x : EM₁ (G , str)) → isProp (B x))
           {x y : EM₁ (G , str)}
           (eq : x ≡ y)
           (bx : B x)
           (by : B y) →
           PathP (λ i → B (eq i)) bx by
  elimEq {B = B} Bprop {x = x} =
    J (λ y eq → ∀ bx by → PathP (λ i → B (eq i)) bx by) (λ bx by → Bprop x bx by)

  elimSet : {B : EM₁ (G , str) → Type ℓ}
          → ((x : EM₁ (G , str)) → isSet (B x))
          → (b : B embase)
          → ((g : G) → PathP (λ i → B (emloop g i)) b b)
          → (x : EM₁ (G , str))
          → B x
  elimSet Bset b bloop embase = b
  elimSet Bset b bloop (emloop g i) = bloop g i
  elimSet Bset b bloop (emcomp g h i j) =
    isSet→SquareP
      (λ i j → Bset (emcomp g h i j))
      (λ j → bloop g j) (λ j → bloop (g + h) j)
      (λ i → b) (λ i → bloop h i)
      i j
  elimSet Bset b bloop (emsquash x y p q r s i j k) =
    isOfHLevel→isOfHLevelDep 3 (λ x → isSet→isGroupoid (Bset x))
      _ _ _ _ (λ j k → g (r j k)) (λ j k → g (s j k)) (emsquash x y p q r s) i j k
    where
      g = elimSet Bset b bloop

  elimProp : {B : EM₁ (G , str) → Type ℓ}
             → ((x : EM₁ (G , str)) → isProp (B x))
             → B embase
             → (x : EM₁ (G , str))
             → B x
  elimProp Bprop b x = elimSet (λ x → isProp→isSet (Bprop x)) b (λ g i → {!Bprop !}) x
{-  elimProp Bprop b embase = b
  elimProp Bprop b (emloop g i) = elimEq Bprop (emloop g) b b i
  elimProp Bprop b (emcomp g h i j) =
    isSet→SquareP (λ i j → isProp→isSet (Bprop (emcomp g h i j)))
      (λ j → elimProp Bprop b (emloop g j))
      (λ j → elimProp Bprop b (emloop (g + h) j))
      (λ i → b)
      (λ i → elimProp Bprop b (emloop h i))
      i j
  elimProp Bprop b (emsquash x y p q r s i j k) =
    isOfHLevel→isOfHLevelDep 3 (λ x → isSet→isGroupoid (isProp→isSet (Bprop x)))
    _ _ _ _ (λ j k → g (r j k)) (λ j k → g (s j k)) (emsquash x y p q r s) i j k
    where
      g = elimProp Bprop b
-}
  elimProp2 : {C : EM₁ (G , str) → EM₁ (G , str) → Type ℓ}
            → ((x y : EM₁ (G , str)) → isProp (C x y))
            → C embase embase
            → (x y : EM₁ (G , str))
            → C x y
  elimProp2 Cprop c = elimProp (λ x → isPropΠ (λ y → Cprop x y))
                               (elimProp (λ y → Cprop embase y) c)

  elim : {B : EM₁ (G , str) → Type ℓ}
       → ((x : EM₁ (G , str)) → isGroupoid (B x))
       → (b : B embase)
       → (bloop : (g : G) → PathP (λ i → B (emloop g i)) b b)
       → ((g h : G) → SquareP (λ i j → B (emcomp g h i j))
            (bloop g) (bloop (g + h)) (λ j → b) (bloop h))
       → (x : EM₁ (G , str))
       → B x
  elim Bgpd b bloop bcomp embase = b
  elim Bgpd b bloop bcomp (emloop g i) = bloop g i
  elim Bgpd b bloop bcomp (emcomp g h i j) = bcomp g h i j
  elim Bgpd b bloop bcomp (emsquash x y p q r s i j k) =
    isOfHLevel→isOfHLevelDep 3 Bgpd
      _ _ _ _ (λ j k → g (r j k)) (λ j k → g (s j k)) (emsquash x y p q r s) i j k
    where
      g = elim Bgpd b bloop bcomp

  rec : {B : Type ℓ}
      → isGroupoid B
      → (b : B)
      → (bloop : G → b ≡ b)
      → ((g h : G) → Square (bloop g) (bloop (g + h)) refl (bloop h))
      → (x : EM₁ (G , str))
      → B
  rec Bgpd = elim (λ _ → Bgpd)
